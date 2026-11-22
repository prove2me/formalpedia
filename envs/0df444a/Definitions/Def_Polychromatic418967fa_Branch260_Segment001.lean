-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch260_Segment001
-- name    : Polychromatic418967fa_Branch260_Segment001
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:47:19.443312+00:00
-- url     : https://prove2.me/theorems/10de7a7c-2397-4d04-a65c-2873b09cb309
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch260_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_260_segment_001 : allB 201 260 :=
  allB_succ' 61 200 260 (Eq.refl Bool.true) (allA_succ_of_gcd 60 200 260 20 3 10 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 200 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 200 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 200 260 2 29 100 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 200 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 200 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 200 260 4 14 50 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 200 260 5 11 40 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 200 260 2 27 100 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 200 260
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 53 200 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 200 260 4 13 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 200 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 200 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 200 260 10 5 20 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 200 260 (accept_3_2 49 200 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 200 260 4 12 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 200 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 47
  200 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 200 260 2 23 100 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 200 260 5 9 40 52
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 200 260 4 11 50
  65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 200 260
  (accept_3_2 43 200 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 200 260 2 21 100 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 200 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 200 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 200 260 20 2 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 200 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 200 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 200 260 2 19 100 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 200 260 (accept_3_2 37 200 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 200 260 4 9 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 200 260 5 7 40 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 200 260 2 17 100 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 200 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 200 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 200 260 4 8 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 200 260 (accept_3_2 31 200 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  200 260 10 3 20 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 200 260 (Polychromatic418967fa.accept_16_13_8_4_1_3250 29 200 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 200 260 4 7 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 200 260 (Polychromatic418967fa.accept_16_11_8_4_1_2234
  27 200 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 200 260 2 13 100 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 200 260 5 5 40 52
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 200 260 4 6 50 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 200 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 200 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 200 260 2 11 100 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 200 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 200 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 200 260 20 1 10 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 200 260 (accept_3_2 19 200 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 200 260 2 9 100 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 200 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 17
  200 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 200 260 4 4 50 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 200 260 5 3 40 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 200 260 2 7 100 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 200 260
  (accept_3_2 13 200 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 200 260 4 3 50 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 200 260
  (Polychromatic418967fa.accept_14_11_4_8_1_664 11 200 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 200 260 10 1 20 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 200 260 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 200 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 200 260 4 2 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 200 260 (accept_3_2 7 200 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 200 260 2 3 100 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 200 260 5 1 40 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 200 260 4 1 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 200 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 200 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 200 260 2 1 100 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 200 260 (accept_3_2 1
  200 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 199 260 (Eq.refl Bool.true)
  (allA_of_3_0 62 199 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 198 260 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 198 260 2 31 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 198 260 (accept_3_2 61 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 198 260 2 30 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 198 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 198 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 198 260 2 29 99 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 198 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 198 260 2 28 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 198 260 (accept_3_2 55 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 198 260 2 27 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 198 260 (Polychromatic418967fa.accept_15_8_3_5_1_608 53 198 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 198 260 2 26 99 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 198 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 198 260 2 25 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 198 260 (accept_3_2 49 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 198 260 2 24 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 198 260 (Polychromatic418967fa.accept_15_2_3_5_1_2991 47 198 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 198 260 2 23 99 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 198 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 198 260 2 22 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 198 260 (accept_3_2 43 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 198 260 2 21 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 198 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 198 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 198 260 2 20 99 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 198 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 198 260 2 19 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 198 260 (accept_3_2 37 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 198 260 2 18 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 198 260 (Polychromatic418967fa.accept_16_3_6_4_1_679 35 198 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 198 260 2 17 99 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 198 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 198 260 2 16 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 198 260 (accept_3_2 31 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 198 260 2 15 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 198 260 (Polychromatic418967fa.accept_14_1_2_8_1_655 29 198 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 198 260 2 14 99 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 198 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 198 260 2 13 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 198 260 (accept_3_2 25 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 198 260 2 12 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 198 260 (Polychromatic418967fa.accept_15_8_3_5_1_608 23 198 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 260 2 11 99 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 198 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 198 260 2 10 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 198 260 (accept_3_2 19 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 260 2 9 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 198 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 198 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 260 2 8 99 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 198 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 198 260 2 7 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 198 260 (accept_3_2 13 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 260 2 6 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 198 260 (Polychromatic418967fa.accept_16_11_6_4_1_2228 11 198 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 198 260 2 5 99 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 198 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 198 260 2 4 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 198 260 (accept_3_2 7 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198
  260 2 3 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  198 260 (Polychromatic418967fa.accept_16_5_6_4_1_3211 5 198 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 198 260 2 2 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 198 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 198 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 198 260 2 1 99 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 260 (accept_3_2 1 198 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 197 260 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 197 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 197 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 197 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 197
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 197 260 (accept_3_2 61 197
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 197 260
  (Polychromatic418967fa.accept_16_12_5_4_1_3275 60 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 197 260 (Polychromatic418967fa.accept_15_14_2_5_1_1272 59 197 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 197 260 (accept_3_2 58 197 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 197 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 197 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 197 260
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 56 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 197 260 (accept_3_2 55 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 197 260 (Polychromatic418967fa.accept_16_6_5_4_1_4330 54 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 197 260 (Polychromatic418967fa.accept_19_15_7_13_1_11844 53 197 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 197 260 (accept_3_2 52 197 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 197 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 197 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 197 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 197 260 (accept_3_2 49 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 197 260 (Polychromatic418967fa.accept_15_3_2_5_1_2980 48 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 197 260 (Polychromatic418967fa.accept_11_3_10_7_1_129 47 197 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 197 260 (accept_3_2 46 197 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 197 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 197 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 197 260
  (Polychromatic418967fa.accept_14_2_1_8_1_650 44 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 197 260 (accept_3_2 43 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 197 260 (Polychromatic418967fa.accept_15_12_2_5_1_3939 42 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 197 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 197 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 197 260 (accept_3_2 40 197 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 197 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 197 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 197 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 197 260 (accept_3_2 37 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 197 260 (Polychromatic418967fa.accept_11_3_10_7_1_129 36 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 197 260 (Polychromatic418967fa.accept_14_7_1_8_1_2873 35 197 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 197 260 (accept_3_2 34 197 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 197 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 197 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 197 260
  (Polychromatic418967fa.accept_17_15_10_5_1_1573 32 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 197 260 (accept_3_2 31 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 197 260 (Polychromatic418967fa.accept_14_2_1_8_1_650 30 197 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 197 260 (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 197
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 260 (accept_3_2 28 197
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 197 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 197 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 197 260 (accept_3_2 25 197 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 197 260 (Polychromatic418967fa.accept_16_8_5_4_1_674 24 197 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 197 260
  (Polychromatic418967fa.accept_14_9_1_8_1_2849 23 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 197 260 (accept_3_2 22 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 197 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 197 260 (Polychromatic418967fa.accept_18_2_17_8_1_1893 20 197 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 197 260 (accept_3_2 19 197 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 197 260 (Polychromatic418967fa.accept_15_3_2_5_1_2980 18 197
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 197 260
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 197 260 (accept_3_2 16 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 197 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 197 260 (Polychromatic418967fa.accept_11_3_10_7_1_129 14 197 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 260 (accept_3_2 13 197 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 197 260 (Polychromatic418967fa.accept_15_12_2_5_1_3939 12 197
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 260
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 197 260 (accept_3_2 10 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  197 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 197 260 (Polychromatic418967fa.accept_16_8_5_4_1_674 8 197 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 260 (accept_3_2 7 197 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 197 260 (Polychromatic418967fa.accept_16_6_5_4_1_4330 6 197 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 260
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 5 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 197 260 (accept_3_2 4 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  197 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 197 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 197 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 197 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 260 (accept_3_2 1 197 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 197 260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65
  196 260 (Eq.refl Bool.true) (allA_of_3_0 65 196 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 195 260
  (Eq.refl Bool.true) (allA_succ_of_gcd 65 195 260 65 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 195 260 (accept_3_2 64 195 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 195 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 195 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 195 260 (Polychromatic418967fa.accept_23_16_11_7_1_15890 62
  195 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 195 260 (accept_3_2 61
  195 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 195 260 5 12 39 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 195 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 195 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 195 260 (accept_3_2 58 195 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 195 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 195 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 195 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 195 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 195 260 5 11 39 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 195 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 195 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 195 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 195 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 195 260 13 4 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 195 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 51
  195 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 195 260 5 10 39 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 195 260 (accept_3_2 49
  195 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 195 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 48 195 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 195 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 195 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 195 260 (accept_3_2 46 195 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 195 260 5 9 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 195 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 195 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 195 260 (accept_3_2 43 195 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 195 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 195
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 195 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 195 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 195 260 5 8 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 195 260 13 3 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 195 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 195 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 195 260 (accept_3_2 37 195 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 195 260 (Polychromatic418967fa.accept_21_15_6_8_1_9888 36 195 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 195 260 5 7 39 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 195 260 (accept_3_2 34
  195 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 195 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 195 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 195 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 195 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 260 (accept_3_2 31 195 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 195 260 5 6 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 195 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 195 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 260 (accept_3_2 28 195 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 195 260 (Polychromatic418967fa.accept_19_8_5_13_1_7800 27 195
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 195 260 13 2 15 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 195 260 5 5 39 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 195 260
  (Polychromatic418967fa.accept_16_8_3_4_1_3233 24 195 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 195 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 195 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 260 (accept_3_2 22 195 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 195 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 195 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 195 260 5 4 39 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 195 260 (accept_3_2 19 195 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 195
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 195 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 260 (accept_3_2 16 195 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  195 260 5 3 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 195 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 195 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 13 195 260 13 1 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 12 195 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 195 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 195 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 195 260 5 2 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 195 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 195 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 260 (Polychromatic418967fa.accept_16_8_3_4_1_3233 8 195 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 260 (accept_3_2 7 195 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 6
  195 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 195 260 5 1 39 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 195 260 (accept_3_2 4
  195 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 195 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 195 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 195 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 260 (accept_3_2 1 195 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 195 260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 194 260
  (Eq.refl Bool.true) (allA_succ_of_gcd 66 194 260 2 33 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 194 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 194 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 194 260 2 32 97 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 194 260
  (Polychromatic418967fa.accept_17_12_7_5_1_8659 63 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 194 260 2 31 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 194 260 (accept_3_2 61 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 194 260 2 30 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 194 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 194 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 194 260 2 29 97 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 194 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 194 260 2 28 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 194 260 (accept_3_2 55 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 194 260 2 27 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 194 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 194 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 194 260 2 26 97 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 194 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 194 260 2 25 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 194 260 (accept_3_2 49 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 194 260 2 24 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 194 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 194 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 194 260 2 23 97 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 194 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 194 260 2 22 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 194 260 (accept_3_2 43 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 194 260 2 21 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 194 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 194 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 194 260 2 20 97 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 194 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 194 260 2 19 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 194 260 (accept_3_2 37 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 194 260 2 18 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 194 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 194 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 194 260 2 17 97 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 194 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 194 260 2 16 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 194 260 (accept_3_2 31 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 194 260 2 15 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 194 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 194 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 194 260 2 14 97 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 194 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 194 260 2 13 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 194 260 (accept_3_2 25 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 194 260 2 12 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 194 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 194 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 194 260 2 11 97 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 194 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 194 260 2 10 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 194 260 (accept_3_2 19 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 194 260 2 9 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 194 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 194 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 194 260 2 8 97 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 194 260 2 7 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 194 260 (accept_3_2 13 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 194 260 2 6 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 194 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 194 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 194 260 2 5 97 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 260
  (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 260 2 4 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 260 (accept_3_2 7 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  260 2 3 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 194 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 260 2 2 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 194 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 260 2 1 97 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 260 (accept_3_2 1 194 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 193 260 (Eq.refl Bool.true)
  (allA_of_3_0 68 193 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 192 260 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 192 260 4 17 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 192 260 (accept_3_2 67 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 192 260 2 33 96 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 192 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 192 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 192 260 4 16 48 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 192 260
  (Polychromatic418967fa.accept_19_6_2_13_1_4945 63 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 192 260 2 31 96 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 192 260 (accept_3_2 61 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 192 260 4 15 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 192 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 192 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 192 260 2 29 96 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 192 260
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 57 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 192 260 4 14 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 192 260 (accept_3_2 55 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 192 260 2 27 96 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 192 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 192 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 192 260 4 13 48 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 192 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 192 260 2 25 96 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 192 260 (accept_3_2 49 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 192 260 4 12 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 192 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 192 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 192 260 2 23 96 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 192 260
  (Polychromatic418967fa.accept_19_7_2_13_1_4935 45 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 192 260 4 11 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 192 260 (accept_3_2 43 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 192 260 2 21 96 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 192 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 192 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 192 260 4 10 48 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 192 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 192 260 2 19 96 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 192 260 (accept_3_2 37 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 192 260 4 9 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 192 260 (Polychromatic418967fa.accept_19_16_2_13_1_13234 35 192 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 192 260 2 17 96 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 192 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 192 260 4 8 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 192 260 (accept_3_2 31 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  192 260 2 15 96 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 192 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 192 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 192 260 4 7 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 192 260 (Polychromatic418967fa.accept_19_8_2_13_1_2328
  27 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 192 260 2 13 96 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 192 260
  (accept_3_2 25 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 192 260 4 6 48 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 192 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 192 260 2 11 96 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 192 260 (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 192 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 192 260 4 5 48 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 192 260 (accept_3_2 19 192 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 192 260 2 9 96 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 192 260
  (Polychromatic418967fa.accept_15_2_12_5_1_2107 17 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 192 260 4 4 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 192 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 192 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 192 260 2 7 96 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 192 260 (accept_3_2 13 192 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 260 4 3 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 192 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 260 2 5 96 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 192 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 192 260 4 2 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 192 260 (accept_3_2 7 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192
  260 2 3 96 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  192 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 192 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 192 260 4 1 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 192 260 (Polychromatic418967fa.accept_18_3_12_8_1_5415 3 192 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 192 260 2 1 96 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 260 (accept_3_2 1 192 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 192 260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 191 260 (Eq.refl Bool.true) (allA_succ_of_accept 69 191 260 (Polychromatic418967fa.accept_6_3_5_2_1_12
  69 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 191 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 191 260 (accept_3_2 67 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 191 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 191 260 (Polychromatic418967fa.accept_19_8_1_13_1_10590 65 191 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 191 260 (accept_3_2 64 191 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 191 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 191 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 191 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 62 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 191 260 (accept_3_2 61 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 191 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 191 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 191 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 191 260 (accept_3_2 58 191 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 191 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 191 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 191 260
  (Polychromatic418967fa.accept_16_8_15_4_1_5402 56 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 191 260 (accept_3_2 55 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 191 260 (Polychromatic418967fa.accept_15_9_11_5_1_1283 54 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 191 260 (Polychromatic418967fa.accept_15_8_11_5_1_169 53 191 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 191 260 (accept_3_2 52 191 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 191 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 191 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 191 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 191 260 (accept_3_2 49 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 191 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 191 260 (Polychromatic418967fa.accept_11_3_4_7_1_114 47 191 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 191 260 (accept_3_2 46 191 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 191 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 191 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 191 260
  (Polychromatic418967fa.accept_16_12_15_4_1_5422 44 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 191 260 (accept_3_2 43 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 191 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 191 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 191 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 191 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 191 260 (accept_3_2 40 191 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 191 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39
  191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 191 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 191 260 (accept_3_2 37 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 191 260 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 191 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 191 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 191 260 (accept_3_2 34 191 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 191 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 191 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 191 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 191 260 (accept_3_2 31 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 191 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 191 260 (Polychromatic418967fa.accept_14_1_9_8_1_2863 29 191 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 191 260 (accept_3_2 28 191 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 191 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 191 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 191 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 191 260 (accept_3_2 25 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 191 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 191 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 191 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 191 260 (accept_3_2 22 191 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 191 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 191 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 191 260 (accept_3_2 19 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 191 260 (Polychromatic418967fa.accept_17_1_4_5_1_3501 18 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 191 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 191 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 260 (accept_3_2 16 191 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 191 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 191 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 191 260 (accept_3_2 13 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 191 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 191 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 191 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 260 (accept_3_2 10 191 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 191 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 260
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 260 (accept_3_2 7 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 191 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 260 (accept_3_2 4 191 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 191 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 260 (accept_3_2 1 191 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 190 260 (Eq.refl Bool.true)
  (allA_of_3_0 71 190 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 189 260 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 189 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 189 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 189 260 (accept_3_2 70 189 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 189 260 (Polychromatic418967fa.accept_14_13_7_8_1_677 69 189 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 189 260
  (Polychromatic418967fa.accept_22_2_13_18_1_6373 68 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 189 260 (accept_3_2 67 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 189 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 189 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 189 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 189 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 189 260 (accept_3_2 64 189 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 189 260 (Polychromatic418967fa.accept_15_3_9_5_1_2082
  63 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 189 260
  (Polychromatic418967fa.accept_14_6_7_8_1_624 62 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 189 260 (accept_3_2 61 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 189 260 (Polychromatic418967fa.accept_16_12_13_4_1_3198 60 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 189 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 189 260 (accept_3_2 58 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 189 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 189 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 189 260
  (Polychromatic418967fa.accept_15_11_9_5_1_2974 56 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 189 260 (accept_3_2 55 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 189 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 189 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 189 260 (accept_3_2 52 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 189 260 (Polychromatic418967fa.accept_22_7_13_18_1_15889 51 189 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 189 260
  (Polychromatic418967fa.accept_17_16_2_5_1_6031 50 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 189 260 (accept_3_2 49 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 189 260 (Polychromatic418967fa.accept_14_6_7_8_1_624 48 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 189 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 189 260 (accept_3_2 46 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 189 260 (Polychromatic418967fa.accept_22_1_13_18_1_15888 45 189 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 189 260
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 44 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 189 260 (accept_3_2 43 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 189 260 (Polychromatic418967fa.accept_11_9_2_7_1_1298 42 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 189 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 260 (accept_3_2 40 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 189 260 (Polychromatic418967fa.accept_16_7_13_4_1_1348 39 189 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 189 260
  (Polychromatic418967fa.accept_16_6_13_4_1_643 38 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 189 260 (accept_3_2 37 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 189 260 (Polychromatic418967fa.accept_19_17_18_13_1_9126 36 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 189 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 189 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 260 (accept_3_2 34 189 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 189 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 189 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 189 260
  (Polychromatic418967fa.accept_23_9_5_7_1_15835 32 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 189 260 (accept_3_2 31 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 189 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 189 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 260 (accept_3_2 28 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 189 260 (Polychromatic418967fa.accept_14_13_7_8_1_677 27 189 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 189 260
  (Polychromatic418967fa.accept_15_11_9_5_1_2974 26 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 189 260 (accept_3_2 25 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 189 260 (Polychromatic418967fa.accept_16_8_13_4_1_3258 24 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 189 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 260 (accept_3_2 22 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 189 260 (Polychromatic418967fa.accept_18_3_9_8_1_2977 21 189 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 189 260
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 189 260 (accept_3_2 19 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 189 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 189 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 260 (accept_3_2 16 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 260 (Polychromatic418967fa.accept_14_1_7_8_1_2063 15 189 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 189 260
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 14 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 189 260 (accept_3_2 13 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 189 260 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 189 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 260 (accept_3_2 10 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 189 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 260
  (Polychromatic418967fa.accept_16_8_13_4_1_3258 8 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 189 260 (accept_3_2 7 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  189 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 189 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 260 (accept_3_2 4 189 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 260 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 189 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 260
  (Polychromatic418967fa.accept_22_2_13_18_1_6373 2 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 189 260 (accept_3_2 1 189 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 188 260 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 188 260 4 18 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 188 260 (Polychromatic418967fa.accept_15_11_8_5_1_1278 71 188 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 188 260 2 35 94 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 188 260
  (Polychromatic418967fa.accept_16_5_12_4_1_4325 69 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 188 260 4 17 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 188 260 (accept_3_2 67 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 188 260 2 33 94 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 188 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 188 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 188 260 4 16 47 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 188 260
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 63 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 188 260 2 31 94 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 188 260 (accept_3_2 61 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 188 260 4 15 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 188 260 (Polychromatic418967fa.accept_15_14_8_5_1_2104 59 188 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 188 260 2 29 94 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 188 260
  (Polychromatic418967fa.accept_15_12_8_5_1_5048 57 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 188 260 4 14 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 188 260 (accept_3_2 55 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 188 260 2 27 94 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 188 260 (Polychromatic418967fa.accept_16_5_12_4_1_4325 53 188 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 188 260 4 13 47 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 188 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 188 260 2 25 94 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 188 260 (accept_3_2 49 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 188 260 4 12 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 188 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 188 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 188 260 2 23 94 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 188 260
  (Polychromatic418967fa.accept_16_13_12_4_1_4323 45 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 188 260 4 11 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 188 260 (accept_3_2 43 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 188 260 2 21 94 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 188 260 (Polychromatic418967fa.accept_15_11_8_5_1_1278 41 188 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 188 260 4 10 47 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 188 260
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 188 260 2 19 94 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 188 260 (accept_3_2 37 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 188 260 4 9 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 188 260 (Polychromatic418967fa.accept_14_7_6_8_1_2856 35 188 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 188 260 2 17 94 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 188 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 33
  188 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 188 260 4 8 47 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 188 260 (accept_3_2 31
  188 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 188 260 2 15 94 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 188 260
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 29 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 188 260 4 7 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 188 260 (Polychromatic418967fa.accept_15_12_8_5_1_5048 27 188 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 188 260 2 13 94 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 188 260 (accept_3_2 25 188 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 188 260 4 6 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 188 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 188 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 188 260 2 11 94 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 188 260
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 21 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 188 260 4 5 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 188 260 (accept_3_2 19 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  188 260 2 9 94 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 188 260 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 188 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 188 260 4 4 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 188 260
  (Polychromatic418967fa.accept_16_15_12_4_1_4324 15 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 188 260 2 7 94 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 188 260 (accept_3_2 13 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 188 260 4 3 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 188 260 (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 188 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 188 260 2 5 94 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 188 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 9
  188 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 188 260 4 2 47 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 188 260 (accept_3_2 7
  188 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188 260 2 3 94 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 188 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 188 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 188 260 4 1 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 188 260 (Polychromatic418967fa.accept_15_3_8_5_1_2105 3 188 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 188 260 2 1 94 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 188 260 (accept_3_2 1 188 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 188 260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 74 187 260 (Eq.refl Bool.true) (allA_of_3_0 74 187 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 75 186 260 (Eq.refl Bool.true) (allA_succ_of_gcd 74 186 260 2 37 93 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 186 260 (accept_3_2 73 186 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 186 260 2 36 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 186 260 (Polychromatic418967fa.accept_15_11_6_5_1_1295
  71 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 186 260 2 35 93 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 186 260
  (Polychromatic418967fa.accept_11_3_10_7_1_129 69 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 186 260 2 34 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 186 260 (accept_3_2 67 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 186 260 2 33 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 186 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 186 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 186 260 2 32 93 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 186 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 186 260 2 31 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 186 260 (accept_3_2 61 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 186 260 2 30 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 186 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 186 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 186 260 2 29 93 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 186 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 186 260 2 28 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 186 260 (accept_3_2 55 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 186 260 2 27 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 186 260 (Polychromatic418967fa.accept_14_11_4_8_1_664 53 186 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 186 260 2 26 93 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 186 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 186 260 2 25 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 186 260 (accept_3_2 49 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 186 260 2 24 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 186 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 186 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 186 260 2 23 93 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 186 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 186 260 2 22 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 186 260 (accept_3_2 43 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 186 260 2 21 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 186 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 186 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 186 260 2 20 93 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 186 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 186 260 2 19 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 186 260 (accept_3_2 37 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 186 260 2 18 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 186 260 (Polychromatic418967fa.accept_17_1_16_5_1_3670 35 186 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 186 260 2 17 93 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 186 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 186 260 2 16 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 186 260 (accept_3_2 31 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 260 2 15 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 186 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 186 260 2 14 93 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 186 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 186 260 2 13 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 186 260 (accept_3_2 25 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 260 2 12 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 186 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 186 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 260 2 11 93 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 186 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 186 260 2 10 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 186 260 (accept_3_2 19 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 260 2 9 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 186 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 260 2 8 93 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 186 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 186 260 2 7 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 186 260 (accept_3_2 13 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 260 2 6 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 186 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 260 2 5 93 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 186 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 186 260 2 4 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 186 260 (accept_3_2 7 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186
  260 2 3 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  186 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 186 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 186 260 2 2 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 186 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 186 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 186 260 2 1 93 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 260 (accept_3_2 1 186 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 185 260 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 185 260 5 15 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 185 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 74 185 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 185 260 (accept_3_2 73 185 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 185 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 185 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 185 260
  (Polychromatic418967fa.accept_11_5_9_7_1_411 71 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 185 260 5 14 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 185 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 185 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 185 260 (Polychromatic418967fa.accept_7_5_3_1_1_424
  68 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 185 260 (accept_3_2 67
  185 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 185 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 66 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 185 260 5 13 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 185 260 (accept_3_2 64 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 185 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 185 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 185 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 185
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 185 260 (accept_3_2 61 185
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 185 260 5 12 37 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 185 260
  (Polychromatic418967fa.accept_16_11_9_4_1_5438 59 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 185 260 (accept_3_2 58 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 185 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 185 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 185 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 185 260 5 11 37 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 185 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 54 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 185 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 185 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 185 260 (accept_3_2 52 185 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 185 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 185 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 185 260 5 10 37 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 185 260 (accept_3_2 49 185 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 185 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 185 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 185 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 185 260 (accept_3_2 46 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  185 260 5 9 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 185 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 185 260 (accept_3_2 43 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 185 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 185 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 185 260 (Polychromatic418967fa.accept_17_7_15_5_1_3649 41 185
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 185 260 5 8 37 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 185 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 185 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 185 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 185 260 (accept_3_2 37 185 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 185 260 (Polychromatic418967fa.accept_21_15_17_8_1_9937 36 185 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 185 260 5 7 37 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 185 260 (accept_3_2 34 185 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 185 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  185 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 185 260 (accept_3_2 31 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  185 260 5 6 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 185 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 185 260 (accept_3_2 28 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 185 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 185 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 185 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 185 260 5 5 37 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 185 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 24 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 185 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 185 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 260 (accept_3_2 22 185 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 185 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 185 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 185 260 5 4 37 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 185 260 (accept_3_2 19 185 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 185 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 185 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 185 260
  (Polychromatic418967fa.accept_18_17_5_8_1_1898 17 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 185 260 (accept_3_2 16 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  185 260 5 3 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 185 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 185 260 (accept_3_2 13 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 185 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 185 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 185 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 185 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 185 260 5 2 37 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 185 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 185 260 (Polychromatic418967fa.accept_16_8_9_4_1_630 8 185 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 260 (accept_3_2 7 185 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 185 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 185 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 185 260 5 1 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 185 260 (accept_3_2 4 185 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 185 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 260 (accept_3_2 1 185 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 184 260 (Eq.refl
  Bool.true) (allA_of_3_0 77 184 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 183 260 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 183 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 183 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 183 260 (accept_3_2 76 183 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 183 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 183 260 (Polychromatic418967fa.accept_9_2_3_8_1_318
  74 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 183 260 (accept_3_2 73
  183 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 183 260
  (Polychromatic418967fa.accept_14_2_1_8_1_650 72 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 183 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 183 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 183 260 (accept_3_2 70 183 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 183 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 183 260 (Polychromatic418967fa.accept_9_5_3_8_1_316
  68 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 183 260 (accept_3_2 67
  183 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 183 260
  (Polychromatic418967fa.accept_12_6_3_8_1_512 66 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 183 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 183 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 183 260 (accept_3_2 64 183 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 183 260 (Polychromatic418967fa.accept_14_7_1_8_1_2873 63 183 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 183 260
  (Polychromatic418967fa.accept_15_2_3_5_1_2991 62 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 183 260 (accept_3_2 61 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 183 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 183 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 183 260 (accept_3_2 58 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 183 260 (Polychromatic418967fa.accept_22_13_7_18_1_12740 57 183 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 183 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 183 260 (accept_3_2 55 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 183 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 183 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 183 260 (accept_3_2 52 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 183 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 183 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 183 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 183 260 (accept_3_2 49 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 183 260 (Polychromatic418967fa.accept_18_12_3_8_1_6817 48 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 183 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 183 260 (accept_3_2 46 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 183 260 (Polychromatic418967fa.accept_16_13_7_4_1_3248 45 183 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 183 260
  (Polychromatic418967fa.accept_14_2_1_8_1_650 44 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 183 260 (accept_3_2 43 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 183 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 183 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 183 260 (accept_3_2 40 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 183 260 (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 183 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 183 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 183 260 (accept_3_2 37 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 183 260 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 183 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 260 (accept_3_2 34 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 183 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 183 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 183 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 183 260 (accept_3_2 31 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 183 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 183 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 260 (accept_3_2 28 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 183 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 183 260
  (Polychromatic418967fa.accept_17_9_13_5_1_3512 26 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 183 260 (accept_3_2 25 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 183 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 183 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 260 (accept_3_2 22 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 260 (Polychromatic418967fa.accept_14_7_1_8_1_2873 21 183 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 183 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 183 260 (accept_3_2 19 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 183 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 183 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 260 (accept_3_2 16 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 183 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 183 260 (accept_3_2 13 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 183 260 (Polychromatic418967fa.accept_16_12_7_4_1_687 12 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 183 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 260 (accept_3_2 10 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 260 (Polychromatic418967fa.accept_14_9_1_8_1_2849 9 183 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 260
  (Polychromatic418967fa.accept_15_8_3_5_1_608 8 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 183 260 (accept_3_2 7 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  183 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 183 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 260 (accept_3_2 4 183 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 183 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 260 (accept_3_2 1 183 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 182 260 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 182 260 26 3 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 182 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 182 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 182 260 2 38 91 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 182 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 75 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 182 260 2 37 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 182 260 (accept_3_2 73 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 182 260 2 36 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 182 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 182 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 182 260 2 35 91 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 182 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 69 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 182 260 2 34 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 182 260 (accept_3_2 67 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 182 260 2 33 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 182 260 13 5 14 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 182 260 2 32 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 182 260 (Polychromatic418967fa.accept_15_3_2_5_1_2980 63 182
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 182 260 2 31 91 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 182 260 (accept_3_2 61
  182 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 182 260 2 30 91 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 182 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 182 260 2 29 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 182 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 182 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 182 260 2 28 91 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 182 260 (accept_3_2 55 182 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 182 260 2 27 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 182 260 (Polychromatic418967fa.accept_12_5_2_8_1_172
  53 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 182 260 26 2 7 10
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 182 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 182 260 2 25 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 182 260 (accept_3_2 49 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 182 260 2 24 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 182 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 182 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 182 260 2 23 91 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 182 260
  (Polychromatic418967fa.accept_11_1_6_7_1_116 45 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 182 260 2 22 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 182 260 (accept_3_2 43 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 182 260 2 21 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 182 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 182 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 182 260 2 20 91 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 182 260 13 3 14 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 182 260 2 19 91 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 182 260 (accept_3_2 37
  182 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 182 260 2 18 91 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 182 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 35 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 182 260 2 17 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 182 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 182 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 182 260 2 16 91 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 182 260 (accept_3_2 31 182 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 182 260 2 15 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 182 260 (Polychromatic418967fa.accept_12_5_2_8_1_172
  29 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 182 260 2 14 91 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 182 260
  (Polychromatic418967fa.accept_15_12_2_5_1_3939 27 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 182 260 26 1 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 182 260 (accept_3_2 25 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24
  182 260 2 12 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 182 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 182 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 182 260 2 11 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 182 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 21
  182 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 182 260 2 10 91 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 182 260 (accept_3_2 19
  182 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 182 260 2 9 91 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 182 260
  (Polychromatic418967fa.accept_12_5_2_8_1_172 17 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 182 260 2 8 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 182 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 182 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 182 260 2 7 91 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 13 182 260 13 1 14 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 182 260 2 6 91 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 182 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 182 260 2 5 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 182 260 (Polychromatic418967fa.accept_17_9_12_5_1_219 9 182 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 182 260 2 4 91 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 182 260 (accept_3_2 7 182 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182 260 2 3 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 182 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 5
  182 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 182 260 2 2 91 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 182 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 3 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 182 260 2 1 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 182 260 (accept_3_2 1 182 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 181 260 (Eq.refl
  Bool.true) (allA_of_3_0 80 181 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 180 260 (Eq.refl Bool.true)
  (allA_succ_of_gcd 80 180 260 20 4 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 180 260 (accept_3_2 79 180 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78
  180 260 2 39 90 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 180 260 (Polychromatic418967fa.accept_21_14_12_8_1_6833 77 180 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 180 260 4 19 45 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 180 260 5 15 36 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 180 260 2 37 90 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 180 260 (accept_3_2 73
  180 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 180 260 4 18 45 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 180 260
  (Polychromatic418967fa.accept_22_5_4_18_1_12818 71 180 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 180 260 10 7 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 180 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 180 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 180 260 4 17 45 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 180 260 (accept_3_2 67 180 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 180 260 2 33 90 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 180 260 5 13 36 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 180 260 4 16 45 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 180 260
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 63 180 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 180 260 2 31 90 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 180 260 (accept_3_2 61 180 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 180 260 20 3 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 180 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 180 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 180 260 2 29 90 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 180 260
  (Polychromatic418967fa.accept_21_15_12_8_1_5275 57 180 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 180 260 4 14 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 55 180 260 5 11 36 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 180 260 2 27 90 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 180 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 53
  180 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 180 260 4 13 45 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 180 260
  (Polychromatic418967fa.accept_21_9_12_8_1_5255 51 180 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 180 260 10 5 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 180 260 (accept_3_2 49 180 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 180 260 4 12 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 180 260 (Polychromatic418967fa.accept_11_3_4_7_1_114 47 180 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 180 260 2 23 90 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 180 260 5 9 36 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 180 260 4 11 45 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 180 260 (accept_3_2 43 180 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 180 260 2 21 90 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 180 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 180 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 180 260 20 2 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 180 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 180 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 180 260 2 19 90 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 180 260 (accept_3_2 37 180 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 180 260 4 9 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 180 260 5 7 36 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 180 260 2 17 90 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 180 260
  (Polychromatic418967fa.accept_22_11_4_18_1_15887 33 180 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 180 260 4 8 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 180 260 (accept_3_2 31 180 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 260 10 3 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 180 260 (Polychromatic418967fa.accept_17_12_10_5_1_4756 29 180 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 260 4 7 45 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 180 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 180 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 180 260 2 13 90 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 180 260 5 5 36 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 180 260 4 6 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 180 260 (Polychromatic418967fa.accept_19_4_9_13_1_7792 23 180 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 260 2 11 90 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 180 260
  (Polychromatic418967fa.accept_23_21_19_7_1_15886 21 180 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 180 260 20 1 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 180 260 (accept_3_2 19 180 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 260 2 9 90 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 180 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 180 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 260 4 4 45 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 180 260 5 3 36 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 180 260 2 7 90 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 260 (accept_3_2 13 180 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 260 4 3 45 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 180 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 180 260 10 1 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 180 260 (Polychromatic418967fa.accept_21_9_12_8_1_5255 9 180 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 180 260 4 2 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 260 (accept_3_2 7 180 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 260 2 3 90 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 180 260 5 1 36 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 180 260 4 1 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 180 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 180 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 180 260 2 1 90 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 260 (accept_3_2 1
  180 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 179 260 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 179 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 179 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 179 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 80
  179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 179 260 (accept_3_2 79
  179 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 179 260
  (Polychromatic418967fa.accept_19_2_8_13_1_9146 78 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 179 260 (Polychromatic418967fa.accept_15_2_14_5_1_2072 77 179 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 179 260 (accept_3_2 76 179 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 179 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 179 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 179 260 (Polychromatic418967fa.accept_12_2_11_8_1_504
  74 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 179 260 (accept_3_2 73
  179 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 179 260
  (Polychromatic418967fa.accept_16_8_3_4_1_3233 72 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 179 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 71 179 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 179 260 (accept_3_2 70 179 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 179 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 179 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 179 260 (Polychromatic418967fa.accept_7_5_4_1_1_412
  68 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 179 260 (accept_3_2 67
  179 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 179 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 66 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 179 260 (Polychromatic418967fa.accept_11_10_3_7_1_2564 65 179 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 179 260 (accept_3_2 64 179 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 179 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 179 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 179 260 (Polychromatic418967fa.accept_12_2_11_8_1_504
  62 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 179 260 (accept_3_2 61
  179 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 179 260
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 60 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 179 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 179 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 179 260 (accept_3_2 58 179 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 179 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 179 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 179 260 (Polychromatic418967fa.accept_16_8_3_4_1_3233
  56 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 179 260 (accept_3_2 55
  179 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 179 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 179 260 (Polychromatic418967fa.accept_15_8_14_5_1_2089 53 179 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 179 260 (accept_3_2 52 179 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 179 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 179 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 179 260 (Polychromatic418967fa.accept_12_2_11_8_1_504
  50 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 179 260 (accept_3_2 49
  179 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 179 260
  (Polychromatic418967fa.accept_11_4_3_7_1_828 48 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 179 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 179 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 179 260 (accept_3_2 46 179 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 179 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 179 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 179 260
  (Polychromatic418967fa.accept_16_12_3_4_1_4317 44 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 179 260 (accept_3_2 43 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 179 260 (Polychromatic418967fa.accept_19_4_8_13_1_7802 42 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 179 260 (Polychromatic418967fa.accept_17_7_9_5_1_2588 41 179 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 179 260 (accept_3_2 40 179 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 179 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 179 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 179 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 179 260 (accept_3_2 37 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 179 260 (Polychromatic418967fa.accept_15_6_14_5_1_2976 36 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 179 260 (Polychromatic418967fa.accept_21_14_11_8_1_5272 35 179 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 179 260 (accept_3_2 34 179 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 179 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 179 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 179 260
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 32 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 179 260 (accept_3_2 31 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 179 260 (Polychromatic418967fa.accept_17_13_9_5_1_6022 30 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 179 260 (Polychromatic418967fa.accept_17_12_9_5_1_799 29 179 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 260 (accept_3_2 28 179 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 179 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 179 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 179 260 (accept_3_2 25 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 179 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 179 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 179 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 260 (accept_3_2 22 179 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 179 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 260
  (Polychromatic418967fa.accept_18_2_17_8_1_1893 20 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 179 260 (accept_3_2 19 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 260 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 179 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 179 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 260 (accept_3_2 16 179 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 179 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 179 260 (accept_3_2 13 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 179 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 179 260 (Polychromatic418967fa.accept_23_11_18_7_1_15885 11 179 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 260 (accept_3_2 10 179 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 179 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 260
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 260 (accept_3_2 7 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 260 (Polychromatic418967fa.accept_15_6_14_5_1_2976 6 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 179 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 260 (accept_3_2 4 179 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 179 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 260 (accept_3_2 1 179 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 178 260 (Eq.refl
  Bool.true) (allA_of_3_0 83 178 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 177 260 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 177 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 177 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 177 260 (accept_3_2 82 177 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 177 260 (Polychromatic418967fa.accept_15_6_12_5_1_2108 81 177 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 177 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 80 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 177 260 (accept_3_2 79 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 177 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 177 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 177 260 (accept_3_2 76 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 177 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 177 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 177 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 74 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 177 260 (accept_3_2 73 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 177 260 (Polychromatic418967fa.accept_11_6_1_7_1_1315 72 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 177 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 177 260 (accept_3_2 70 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 177 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 177 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 177 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 177 260 (accept_3_2 67 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 177 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 177 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 177 260 (accept_3_2 64 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 177 260 (Polychromatic418967fa.accept_17_12_7_5_1_8659 63 177 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 177 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 62 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 177 260 (accept_3_2 61 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 177 260 (Polychromatic418967fa.accept_16_12_1_4_1_5403 60 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 177 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 177 260 (accept_3_2 58 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 177 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 177 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 177 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 177 260 (accept_3_2 55 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 177 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 177 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 177 260 (accept_3_2 52 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 177 260 (Polychromatic418967fa.accept_15_6_12_5_1_2108 51 177 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 177 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 177 260 (accept_3_2 49 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 177 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 177 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 260 (accept_3_2 46 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 177 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 177 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 177 260
  (Polychromatic418967fa.accept_16_12_1_4_1_5403 44 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 177 260 (accept_3_2 43 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 177 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 177 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 260 (accept_3_2 40 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 177 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 177 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 177 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 177 260 (accept_3_2 37 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 177 260 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 177 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 260 (accept_3_2 34 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 177 260 (Polychromatic418967fa.accept_21_12_9_8_1_2370 33 177 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 177 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 177 260 (accept_3_2 31 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 177 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 177 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 260 (accept_3_2 28 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 177 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 177 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 260
  (Polychromatic418967fa.accept_17_9_7_5_1_1566 26 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 177 260 (accept_3_2 25 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 177 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 177 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 260 (accept_3_2 22 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 177 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 177 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 177 260 (accept_3_2 19 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 177 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 177 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 260 (accept_3_2 16 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 177 260 (Polychromatic418967fa.accept_14_1_9_8_1_2863 15 177 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 260 (accept_3_2 13 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 177 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 177 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 260 (accept_3_2 10 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 177 260 (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 177 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 260
  (Polychromatic418967fa.accept_15_8_12_5_1_2987 8 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 177 260 (accept_3_2 7 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  177 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 177 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 260 (accept_3_2 4 177 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 177 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 177 260 (accept_3_2 1 177 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 176 260
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 176 260 4 21 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 176 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 176 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 176 260 2 41 88 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 176 260
  (Polychromatic418967fa.accept_15_6_11_5_1_168 81 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 176 260 4 20 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 176 260 (accept_3_2 79 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 176 260 2 39 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 176 260 (Polychromatic418967fa.accept_15_2_11_5_1_1266 77 176 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 176 260 4 19 44 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 176 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 75 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 176 260 2 37 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 176 260 (accept_3_2 73 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 176 260 4 18 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 176 260 (Polychromatic418967fa.accept_17_3_6_5_1_8669 71 176 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 176 260 2 35 88 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 176 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 69 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 176 260 4 17 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 176 260 (accept_3_2 67 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 176 260 2 33 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 176 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 176 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 176 260 4 16 44 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 176 260
  (Polychromatic418967fa.accept_23_17_15_7_1_11085 63 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 176 260 2 31 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 176 260 (accept_3_2 61 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 176 260 4 15 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 176 260 (Polychromatic418967fa.accept_18_5_14_8_1_2966 59 176 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 176 260 2 29 88 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 176 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 176 260 4 14 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 176 260 (accept_3_2 55 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 176 260 2 27 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 176 260 (Polychromatic418967fa.accept_15_8_11_5_1_169 53 176 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 176 260 4 13 44 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 176 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 176 260 2 25 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 176 260 (accept_3_2 49 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 176 260 4 12 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 176 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 176 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 176 260 2 23 88 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 176 260
  (Polychromatic418967fa.accept_17_11_6_5_1_3662 45 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 176 260 4 11 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 176 260 (accept_3_2 43 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 176 260 2 21 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 176 260 (Polychromatic418967fa.accept_18_5_14_8_1_2966 41 176 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 176 260 4 10 44 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 176 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 176 260 2 19 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 176 260 (accept_3_2 37 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 176 260 4 9 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 176 260 (Polychromatic418967fa.accept_17_1_6_5_1_3502 35 176 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 176 260 2 17 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 176 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 33
  176 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 176 260 4 8 44 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 176 260 (accept_3_2 31
  176 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 176 260 2 15 88 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 176 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 176 260 4 7 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 176 260 (Polychromatic418967fa.accept_19_8_5_13_1_7800 27 176 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 176 260 2 13 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 176 260 (accept_3_2 25 176 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 176 260 4 6 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 176 260 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 176
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 260 2 11 88 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 176 260 4 5 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 176 260 (accept_3_2 19 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  176 260 2 9 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 176 260 (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 176 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 260 4 4 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 15
  176 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 176 260 2 7 88 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 176 260 (accept_3_2 13
  176 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 176 260 4 3 44 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 176 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 176 260 2 5 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 176 260 (Polychromatic418967fa.accept_15_9_11_5_1_1283 9 176 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 176 260 4 2 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 176 260 (accept_3_2 7 176 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176 260 2 3 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 176 260 (Polychromatic418967fa.accept_18_5_14_8_1_2966 5 176 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 176 260 4 1 44 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 176 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 176 260 2 1 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 176 260 (accept_3_2 1 176 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 175 260
  (Eq.refl Bool.true) (allA_of_3_0 86 175 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 174 260 (Eq.refl
  Bool.true) (allA_succ_of_gcd 86 174 260 2 43 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 174 260 (accept_3_2 85 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 174 260 2 42 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 174 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 174 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 174 260 2 41 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 174 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 174 260 2 40 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 174 260 (accept_3_2 79 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 174 260 2 39 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 174 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 174 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 174 260 2 38 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 174 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 75 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 174 260 2 37 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 174 260 (accept_3_2 73 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 174 260 2 36 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 174 260 (Polychromatic418967fa.accept_11_5_9_7_1_411 71 174 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 174 260 2 35 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 174 260
  (Polychromatic418967fa.accept_9_6_3_8_1_595 69 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 174 260 2 34 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 174 260 (accept_3_2 67 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 174 260 2 33 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 174 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 174 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 174 260 2 32 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 174 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 174 260 2 31 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 174 260 (accept_3_2 61 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 174 260 2 30 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 174 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 174 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 174 260 2 29 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 174 260
  (Polychromatic418967fa.accept_11_2_9_7_1_124 57 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 174 260 2 28 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 174 260 (accept_3_2 55 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 174 260 2 27 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 174 260 (Polychromatic418967fa.accept_22_9_20_18_1_8035 53 174 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 174 260 2 26 87 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 174 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 174 260 2 25 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 174 260 (accept_3_2 49 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 260 2 24 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 174 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 174 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 174 260 2 23 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 174 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 174 260 2 22 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 174 260 (accept_3_2 43 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 260 2 21 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 174 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 174 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 174 260 2 20 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 174 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 174 260 2 19 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 174 260 (accept_3_2 37 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 260 2 18 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 260 (Polychromatic418967fa.accept_11_2_9_7_1_124 35 174 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 174 260 2 17 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 174 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 174 260 2 16 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 174 260 (accept_3_2 31 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 260 2 15 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 174 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 260 2 14 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 174 260
  (Polychromatic418967fa.accept_11_5_9_7_1_411 27 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 174 260 2 13 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 174 260 (accept_3_2 25 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 260 2 12 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 174 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 260 2 11 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 174 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 174 260 2 10 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 174 260 (accept_3_2 19 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 260 2 9 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 260 (Polychromatic418967fa.accept_16_1_14_4_1_3220 17 174 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 260 2 8 87 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 174 260
  (Polychromatic418967fa.accept_9_6_3_8_1_595 15 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 174 260 2 7 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 174 260 (accept_3_2 13 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 260 2 6 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 174 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 260 2 5 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 174 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 174 260 2 4 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 174 260 (accept_3_2 7 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174
  260 2 3 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  174 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 174 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 174 260 2 2 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 174 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 174 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 260 2 1 87 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 260 (accept_3_2 1 174 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 173 260
  (Eq.refl Bool.true) (allA_succ_of_accept 87 173 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 173 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 173 260 (accept_3_2 85 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 173 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 173 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 173 260 (accept_3_2 82 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 173 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 173 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 80 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 173 260 (accept_3_2 79 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 173 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 173 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 173 260 (accept_3_2 76 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 173 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 173 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 74 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 173 260 (accept_3_2 73 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 173 260 (Polychromatic418967fa.accept_15_12_8_5_1_5048 72 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 173 260 (Polychromatic418967fa.accept_15_11_8_5_1_1278 71 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 173 260 (accept_3_2 70 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 173 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 173 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 173 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 173 260 (accept_3_2 67 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 173 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 173 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 65 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 173 260 (accept_3_2 64 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 173 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 173 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 62 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 173 260 (accept_3_2 61 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 173 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 173 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 173 260 (accept_3_2 58 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 173 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 173 260
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 56 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 173 260 (accept_3_2 55 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 173 260 (Polychromatic418967fa.accept_16_6_13_4_1_643 54 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 173 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 173 260 (accept_3_2 52 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 173 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 173 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 173 260 (accept_3_2 49 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 173 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 173 260 (Polychromatic418967fa.accept_22_3_19_18_1_12781 47 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 173 260 (accept_3_2 46 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 173 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 173 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 173 260
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 44 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 173 260 (accept_3_2 43 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 173 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 173 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 173 260 (accept_3_2 40 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 173 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 173 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 173 260 (accept_3_2 37 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 173 260 (Polychromatic418967fa.accept_17_2_3_5_1_763 36 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 173 260 (Polychromatic418967fa.accept_19_16_2_13_1_13234 35 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 260 (accept_3_2 34 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 173 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 173 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 173 260 (accept_3_2 31 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 173 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 173 260 (Polychromatic418967fa.accept_15_14_8_5_1_2104 29 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 173 260 (accept_3_2 28 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 173 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 173 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 260
  (Polychromatic418967fa.accept_11_4_8_7_1_819 26 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 173 260 (accept_3_2 25 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 173 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 173 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 260 (accept_3_2 22 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 173 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 173 260 (accept_3_2 19 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 173 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 173 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 260 (accept_3_2 16 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 173 260 (accept_3_2 13 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 260 (accept_3_2 10 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 260
  (Polychromatic418967fa.accept_16_8_13_4_1_3258 8 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 260 (accept_3_2 7 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 260 (accept_3_2 4 173 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 173 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 260 (accept_3_2 1 173 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 172 260
  (Eq.refl Bool.true) (allA_of_3_0 89 172 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 171 260 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 171 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 171 260 (accept_3_2 88 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 171 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 171 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 171 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 86 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 171 260 (accept_3_2 85 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 171 260 (Polychromatic418967fa.accept_17_16_1_5_1_2600 84 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 171 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 171 260 (accept_3_2 82 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 171 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 171 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 171 260
  (Polychromatic418967fa.accept_21_17_3_8_1_6793 80 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 171 260 (accept_3_2 79 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 171 260 (Polychromatic418967fa.accept_11_1_6_7_1_116 78 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 171 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 171 260 (accept_3_2 76 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 171 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 171 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 171 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 74 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 171 260 (accept_3_2 73 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 171 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 171 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 171 260 (accept_3_2 70 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 171 260 (Polychromatic418967fa.accept_21_6_3_8_1_9928 69 171 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 171 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 68 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 171 260 (accept_3_2 67 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 171 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 171 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 171 260 (accept_3_2 64 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 171 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 171 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 171 260
  (Polychromatic418967fa.accept_23_16_10_7_1_12648 62 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 171 260 (accept_3_2 61 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 171 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 171 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 171 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 171 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 171 260 (accept_3_2 58 171 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 171 260
  (Polychromatic418967fa.accept_15_12_6_5_1_1275 57 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 171 260 (Polychromatic418967fa.accept_11_1_6_7_1_116 56 171 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 260 (accept_3_2 55 171 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 171 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 171 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53
  171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 171 260 (accept_3_2 52
  171 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 171 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 171 260 (Polychromatic418967fa.accept_17_16_1_5_1_2600 50 171 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 260 (accept_3_2 49 171 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 171 260 (Polychromatic418967fa.accept_15_3_6_5_1_2079 48 171 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 171 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 171 260 (accept_3_2 46 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 171 260 (Polychromatic418967fa.accept_11_1_6_7_1_116 45 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 171 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 260 (accept_3_2 43 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 171 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 171 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 171 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 171 260 (accept_3_2 40 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 171 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 171 260 (Polychromatic418967fa.accept_16_6_11_4_1_635 38 171 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 260 (accept_3_2 37 171 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 260 (Polychromatic418967fa.accept_21_15_3_8_1_6822 36 171
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 260 (accept_3_2 34 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 171 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 171 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 260 (accept_3_2 31 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 171 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 171 260 (accept_3_2 28 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 171 260 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 171 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 260 (accept_3_2 25 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 260 (Polychromatic418967fa.accept_16_8_11_4_1_3290 24 171 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 260 (accept_3_2 22 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 171 260 (Polychromatic418967fa.accept_17_4_1_5_1_2554 21 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 171 260 (Polychromatic418967fa.accept_22_20_17_18_1_11276 20 171 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 260 (accept_3_2 19 171 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 171 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 260 (accept_3_2 16 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 171 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 171 260 (Polychromatic418967fa.accept_15_14_6_5_1_7215 14 171 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 260 (accept_3_2 13 171 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 171 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 260 (accept_3_2 10 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  171 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 171 260 (Polychromatic418967fa.accept_16_8_11_4_1_3290 8 171 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 260 (accept_3_2 7 171 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 171 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 260 (accept_3_2 4 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 260 (Polychromatic418967fa.accept_15_3_6_5_1_2079 3 171 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 260 (accept_3_2 1 171 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 171
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 170 260
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 170 260 10 9 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 170 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 89 170 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 170 260 2 44 85 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 170 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 87 170 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 170 260 2 43 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 85 170 260 5 17 34 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 170 260 2 42 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 170 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 170 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 170 260 2 41 85 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 170 260
  (Polychromatic418967fa.accept_19_5_18_13_1_9116 81 170 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 170 260 10 8 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 170 260 (accept_3_2 79 170 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 170 260 2 39 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 170 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 170 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 170 260 2 38 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 170 260 5 15 34 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 170 260 2 37 85 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 170 260 (accept_3_2 73
  170 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 170 260 2 36 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 170 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 71 170 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 170 260 10 7 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 170 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 170 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 170 260 2 34 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 170 260 (accept_3_2 67 170 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 170 260 2 33 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 170 260 5 13 34 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 170 260 2 32 85 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 170 260
  (Polychromatic418967fa.accept_27_9_8_17_1_15884 63 170 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 170 260 2 31 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 170 260 (accept_3_2 61 170 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 170 260 10 6 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 170 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 170 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 170 260 2 29 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 170 260
  (Polychromatic418967fa.accept_14_1_2_8_1_655 57 170 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 170 260 2 28 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 170 260 5 11 34 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 170 260 2 27 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 170 260 (Polychromatic418967fa.accept_11_9_5_7_1_815 53 170 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 170 260 2 26 85 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 170 260
  (Polychromatic418967fa.accept_23_5_9_7_1_15883 51 170 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 170 260 10 5 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 170 260 (accept_3_2 49 170 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 170 260 2 24 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 170 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 170 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 170 260 2 23 85 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 170 260 5 9 34 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 170 260 2 22 85 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 170 260 (accept_3_2 43
  170 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 170 260 2 21 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 170 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 170 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 170 260 10 4 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 170 260 (Polychromatic418967fa.accept_19_1_18_13_1_7796 39 170 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 170 260 2 19 85 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 170 260 (accept_3_2 37 170 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 170 260 2 18 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 170 260 5 7 34 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 170 260 2 17 85 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 260
  (Polychromatic418967fa.accept_19_14_18_13_1_7823 33 170 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 170 260 2 16 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 170 260 (accept_3_2 31 170 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 170 260 10 3 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 170 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 170 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 170 260 2 14 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 170 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 170 260 2 13 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 170 260 5 5 34 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 170 260 2 12 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 170 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 170 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 260 2 11 85 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 260
  (Polychromatic418967fa.accept_23_21_9_7_1_9349 21 170 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 170 260 10 2 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 170 260 (accept_3_2 19 170 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 260 2 9 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 170 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 260 2 8 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 170 260 5 3 34 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 170 260 2 7 85 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 170 260 (accept_3_2 13 170 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 170 260 2 6 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 170 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 170 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 170 260 10 1 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 170 260 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 170 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 170 260 2 4 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 170 260 (accept_3_2 7 170 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170 260 2 3 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 170 260 5 1 34 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 170 260 2 2 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 170 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  170 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 260 2 1 85 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 260 (accept_3_2 1
  170 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 169 260
  (Eq.refl Bool.true) (allA_of_3_0 92 169 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 168 260 (Eq.refl
  Bool.true) (allA_succ_of_gcd 92 168 260 4 23 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 168 260 (accept_3_2 91 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 168 260 2 45 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 168 260 (Polychromatic418967fa.accept_16_9_8_4_1_1354 89 168 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 168 260 4 22 42 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 168 260
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 87 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 168 260 2 43 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 168 260 (accept_3_2 85 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 168 260 4 21 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 168 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 83 168 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 168 260 2 41 84 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 168 260
  (Polychromatic418967fa.accept_11_4_3_7_1_828 81 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 168 260 4 20 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 168 260 (accept_3_2 79 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 168 260 2 39 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 168 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 168 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 168 260 4 19 42 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 168 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 75 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 168 260 2 37 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 168 260 (accept_3_2 73 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 168 260 4 18 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 168 260 (Polychromatic418967fa.accept_16_7_8_4_1_689 71 168 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 168 260 2 35 84 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 168 260
  (Polychromatic418967fa.accept_15_9_3_5_1_2077 69 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 168 260 4 17 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 168 260 (accept_3_2 67 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 168 260 2 33 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 168 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 168 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 168 260 4 16 42 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 168 260
  (Polychromatic418967fa.accept_16_15_8_4_1_1355 63 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 168 260 2 31 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 168 260 (accept_3_2 61 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 168 260 4 15 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 168 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 168 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 168 260 2 29 84 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 168 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 168 260 4 14 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 168 260 (accept_3_2 55 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 168 260 2 27 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 168 260 (Polychromatic418967fa.accept_15_8_3_5_1_608 53 168 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 168 260 4 13 42 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 168 260
  (Polychromatic418967fa.accept_15_6_3_5_1_607 51 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 168 260 2 25 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 168 260 (accept_3_2 49 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 168 260 4 12 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 168 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 168 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 168 260 2 23 84 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 168 260
  (Polychromatic418967fa.accept_16_13_8_4_1_3250 45 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 168 260 4 11 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 168 260 (accept_3_2 43 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 260 2 21 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 168 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 168 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 168 260 4 10 42 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 168 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 168 260 2 19 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 168 260 (accept_3_2 37 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 168 260 4 9 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 168 260 (Polychromatic418967fa.accept_16_3_8_4_1_3279 35 168 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 260 2 17 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 168 260 (Polychromatic418967fa.accept_16_1_8_4_1_4334
  33 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 168 260 4 8 42 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 168 260
  (accept_3_2 31 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 168 260 2 15 84 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 168 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 168 260 4 7 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 168 260 (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 168 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 168 260 2 13 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 260 (accept_3_2 25 168 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 168 260 4 6 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 168 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 168 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 260 2 11 84 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 168 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 168 260 4 5 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 168 260 (accept_3_2 19 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  168 260 2 9 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 168 260 (Polychromatic418967fa.accept_15_2_3_5_1_2991 17 168 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 260 4 4 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 168 260 (Polychromatic418967fa.accept_11_4_3_7_1_828
  15 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 168 260 2 7 84 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 260
  (accept_3_2 13 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 260 4 3 42 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 168 260 2 5 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 168 260 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 168 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 168 260 4 2 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 168 260 (accept_3_2 7 168 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 260 2 3 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 168 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168 260 4 1 42 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 168 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 168 260 2 1 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 168 260 (accept_3_2 1 168 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 167
  260 (Eq.refl Bool.true) (allA_succ_of_accept 93 167 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 167 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 92 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 167 260 (accept_3_2 91 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 167 260 (Polychromatic418967fa.accept_19_14_15_13_1_4898 90 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 89 167 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 89 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 167 260 (accept_3_2 88 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 167 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 167 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 167 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 86 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 167 260 (accept_3_2 85 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 167 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 167 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 83 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 167 260 (accept_3_2 82 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 167 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 167 260
  (Polychromatic418967fa.accept_19_4_15_13_1_13215 80 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 167 260 (accept_3_2 79 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 167 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 167 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 167 260 (Polychromatic418967fa.accept_14_7_13_8_1_2067 77 167
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 167 260 (accept_3_2 76 167
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 167 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 75 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 167 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 167 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 167 260 (accept_3_2 73 167 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 167 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 167 260
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 71 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 167 260 (accept_3_2 70 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 167 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 167 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 167 260 (accept_3_2 67 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 167 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 167 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 167 260 (accept_3_2 64 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 167 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 167 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 167 260 (accept_3_2 61 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 167 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 167 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 167 260
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 167 260 (accept_3_2 58 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 167 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 167 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 167 260 (accept_3_2 55 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 167 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 167 260
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 53 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 167 260 (accept_3_2 52 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 167 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 167 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 167 260 (accept_3_2 49 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 167 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 167 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 167 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 167 260 (accept_3_2 46 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 167 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 167 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 167 260 (accept_3_2 43 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 167 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 167 260
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 41 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 167 260 (accept_3_2 40 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 167 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 167 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 167 260 (accept_3_2 37 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 167 260 (Polychromatic418967fa.accept_17_2_14_5_1_2575 36 167 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 167 260
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 167 260 (accept_3_2 34 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 167 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 167 260 (Polychromatic418967fa.accept_18_14_5_8_1_1880 32 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 167 260 (accept_3_2 31 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 167 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 167 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 167 260 (accept_3_2 28 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 167 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 167 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 260 (accept_3_2 25 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 167 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 167 260 (accept_3_2 22 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 167 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 167 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 260 (accept_3_2 19 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 260 (Polychromatic418967fa.accept_15_3_2_5_1_2980 18 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 260
  (Polychromatic418967fa.accept_18_17_5_8_1_1898 17 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 167 260 (accept_3_2 16 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 260 (accept_3_2 13 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 167 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 260
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 260 (accept_3_2 10 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 260 (Polychromatic418967fa.accept_16_8_7_4_1_2217 8 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 260 (accept_3_2 7 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 167 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 260 (accept_3_2 4 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 167 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 260 (accept_3_2 1 167 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 166
  260 (Eq.refl Bool.true) (allA_of_3_0 95 166 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 96 165 260
  (Eq.refl Bool.true) (allA_succ_of_gcd 95 165 260 5 19 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 165 260 (accept_3_2 94 165 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 165 260 (Polychromatic418967fa.accept_17_8_12_5_1_1577 93 165 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 165 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 92 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 165 260 (accept_3_2 91 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90
  165 260 5 18 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 165 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 165 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 165 260 (accept_3_2 88 165 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 165 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 165 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 165 260 (Polychromatic418967fa.accept_9_5_3_8_1_316
  86 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 165 260 5 17 33 52
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 165 260
  (Polychromatic418967fa.accept_18_12_3_8_1_6817 84 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 165 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 165 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 165 260 (accept_3_2 82 165 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 165 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 81 165 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 165 260 5 16 33 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 165 260 (accept_3_2 79 165 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 165 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 165 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 165 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 165 260 (accept_3_2 76 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75
  165 260 5 15 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 165 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 74 165 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 165 260 (accept_3_2 73 165 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 165 260 (Polychromatic418967fa.accept_16_8_5_4_1_674 72 165 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 165 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 165 260 5 14 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 165 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 165 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 165 260 (Polychromatic418967fa.accept_7_5_4_1_1_412
  68 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 165 260 (accept_3_2 67
  165 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 165 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 66 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 165 260 5 13 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 165 260 (accept_3_2 64 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 165 260 (Polychromatic418967fa.accept_16_15_5_4_1_6678 63 165 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 165 260 (Polychromatic418967fa.accept_23_16_4_7_1_11092 62 165
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 260 (accept_3_2 61 165
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 165 260 5 12 33 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 165 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 165 260 (accept_3_2 58 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 165 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 165 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 165 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 165 260 5 11 33 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 165 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 165 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 165 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 165 260 (accept_3_2 52 165 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 165 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 165 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 165 260 5 10 33 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 165 260 (accept_3_2 49 165 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 260 (Polychromatic418967fa.accept_18_12_3_8_1_6817 48 165
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 165 260 (accept_3_2 46 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  165 260 5 9 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 165 260 (Polychromatic418967fa.accept_16_12_5_4_1_3275 44 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 165 260 (accept_3_2 43 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 165 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 165 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 165 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 165 260 5 8 33 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 165 260
  (Polychromatic418967fa.accept_22_17_11_18_1_15869 39 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 165 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 165 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 260 (accept_3_2 37 165 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 260 (Polychromatic418967fa.accept_21_15_18_8_1_6809 36 165 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 165 260 5 7 33 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 165 260 (accept_3_2 34
  165 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 165 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 165 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 165 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 260 (accept_3_2 31 165 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 165 260 5 6 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 165 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 165 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 260 (accept_3_2 28 165 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 165 260 (Polychromatic418967fa.accept_17_10_12_5_1_6028 27 165
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 165 260 5 5 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 165 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 165 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 165 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 260 (accept_3_2 22 165 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 165 260
  (Polychromatic418967fa.accept_22_21_11_18_1_15882 21 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 165 260 5 4 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 165 260 (accept_3_2 19 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 165 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 165 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 165 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 260 (accept_3_2 16 165 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 260 5 3 33 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 165 260 (accept_3_2 13 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 165 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 165 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 165 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 165 260 5 2 33 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 165 260
  (Polychromatic418967fa.accept_8_1_5_4_1_388 9 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 165 260 (Polychromatic418967fa.accept_16_8_5_4_1_674 8 165 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 260 (accept_3_2 7 165 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 165 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 165 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 165 260 5 1 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 165 260 (accept_3_2 4 165 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 165 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 260 (accept_3_2 1 165 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 164
  260 (Eq.refl Bool.true) (allA_succ_of_gcd 96 164 260 4 24 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 164 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 95 164 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 164 260 2 47 82 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 164 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 93 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 164 260 4 23 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 164 260 (accept_3_2 91 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 164 260 2 45 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 164 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 164 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 164 260 4 22 41 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 164 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 87 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 164 260 2 43 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 164 260 (accept_3_2 85 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 164 260 4 21 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 164 260 (Polychromatic418967fa.accept_15_8_14_5_1_2089 83 164 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 164 260 2 41 82 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 164 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 81 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 164 260 4 20 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 164 260 (accept_3_2 79 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 164 260 2 39 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 164 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 164 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 164 260 4 19 41 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 164 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 75 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 164 260 2 37 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 164 260 (accept_3_2 73 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 164 260 4 18 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 164 260 (Polychromatic418967fa.accept_18_17_2_8_1_6800 71 164 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 164 260 2 35 82 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 164 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 69 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 164 260 4 17 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 164 260 (accept_3_2 67 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 164 260 2 33 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 164 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 164 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 164 260 4 16 41 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 164 260
  (Polychromatic418967fa.accept_19_6_12_13_1_14522 63 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 164 260 2 31 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 164 260 (accept_3_2 61 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 164 260 4 15 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 164 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 164 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 164 260 2 29 82 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 164 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 164 260 4 14 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 164 260 (accept_3_2 55 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 164 260 2 27 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 164 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 164 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 164 260 4 13 41 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 164 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 164 260 2 25 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 164 260 (accept_3_2 49 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 164 260 4 12 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 164 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 164 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 164 260 2 23 82 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 260
  (Polychromatic418967fa.accept_21_3_17_8_1_8402 45 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 164 260 4 11 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 164 260 (accept_3_2 43 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 164 260 2 21 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 164 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 164 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 260 4 10 41 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 260 2 19 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 260 (accept_3_2 37 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 260 4 9 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 164 260 (Polychromatic418967fa.accept_18_17_2_8_1_6800 35 164 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 260 2 17 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 33
  164 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 164 260 4 8 41 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 164 260 (accept_3_2 31
  164 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 164 260 2 15 82 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 164 260
  (Polychromatic418967fa.accept_25_4_14_10_1_15881 29 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 164 260 4 7 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 164 260 (Polychromatic418967fa.accept_23_4_3_7_1_15880 27 164 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 164 260 2 13 82 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 164 260 (accept_3_2 25 164 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 164 260 4 6 41 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 164 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 164 260 2 11 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 164 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 164 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 164 260 4 5 41 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 164 260 (accept_3_2 19 164 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 164 260 2 9 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 164 260 (Polychromatic418967fa.accept_15_2_14_5_1_2072
  17 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 260 4 4 41 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 164 260 2 7 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 164 260 (accept_3_2 13 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 164 260 4 3 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 164 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 164 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 164 260 2 5 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 9
  164 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 164 260 4 2 41 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 164 260 (accept_3_2 7
  164 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164 260 2 3 82 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 164 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 164 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 164 260 4 1 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 164 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 164 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 260 2 1 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 260 (accept_3_2 1 164 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 164
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  163 260 (Eq.refl Bool.true) (allA_of_3_0 98 163 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 99 162 260
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 162 260 2 49 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 162 260 (accept_3_2 97 162 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 162 260 2 48 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 162 260 (Polychromatic418967fa.accept_22_7_8_18_1_6355 95 162 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 162 260 2 47 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 162 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 93 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 162 260 2 46 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 162 260 (accept_3_2 91 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 162 260 2 45 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 162 260 (Polychromatic418967fa.accept_21_5_15_8_1_9935 89 162 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 162 260 2 44 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 162 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 87 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 162 260 2 43 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 162 260 (accept_3_2 85 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 162 260 2 42 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 162 260 (Polychromatic418967fa.accept_15_8_12_5_1_2987 83 162 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 162 260 2 41 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 162 260
  (Polychromatic418967fa.accept_11_4_8_7_1_819 81 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 162 260 2 40 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 162 260 (accept_3_2 79 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 162 260 2 39 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 162 260 (Polychromatic418967fa.accept_15_2_12_5_1_2107 77 162 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 162 260 2 38 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 162 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 75 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 162 260 2 37 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 162 260 (accept_3_2 73 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 162 260 2 36 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 162 260 (Polychromatic418967fa.accept_23_2_1_7_1_15858 71 162 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 162 260 2 35 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 162 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 162 260 2 34 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 162 260 (accept_3_2 67 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 162 260 2 33 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 162 260 (Polychromatic418967fa.accept_17_14_9_5_1_4755 65 162 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 162 260 2 32 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 162 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 162 260 2 31 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 162 260 (accept_3_2 61 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 162 260 2 30 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 162 260 (Polychromatic418967fa.accept_11_4_8_7_1_819 59 162 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 162 260 2 29 81 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 162 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 162 260 2 28 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 162 260 (accept_3_2 55 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 260 2 27 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 162 260 (Polychromatic418967fa.accept_15_8_12_5_1_2987 53 162 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 162 260 2 26 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 162 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 162 260 2 25 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 162 260 (accept_3_2 49 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 260 2 24 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 162 260 (Polychromatic418967fa.accept_15_2_12_5_1_2107 47 162 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 260 2 23 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 162 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 162 260 2 22 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 162 260 (accept_3_2 43 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 260 2 21 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 162 260 (Polychromatic418967fa.accept_17_7_9_5_1_2588 41 162 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 260 2 20 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 162 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 162 260 2 19 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 162 260 (accept_3_2 37 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 260 2 18 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 260 (Polychromatic418967fa.accept_19_16_10_13_1_4922 35 162 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 260 2 17 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 162 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 162 260 2 16 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 162 260 (accept_3_2 31 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 260 2 15 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 260 (Polychromatic418967fa.accept_17_12_9_5_1_799 29 162 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 260 2 14 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 162 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 162 260 2 13 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 162 260 (accept_3_2 25 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 260 2 12 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 260 (Polychromatic418967fa.accept_15_8_12_5_1_2987 23 162 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 260 2 11 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 162 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 162 260 2 10 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 162 260 (accept_3_2 19 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 260 2 9 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 260 (Polychromatic418967fa.accept_15_2_12_5_1_2107 17 162 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 260 2 8 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 162 260
  (Polychromatic418967fa.accept_11_4_8_7_1_819 15 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 162 260 2 7 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 162 260 (accept_3_2 13 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 260 2 6 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 162 260 (Polychromatic418967fa.accept_25_11_12_10_1_15879 11 162 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 260 2 5 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 162 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 162 260 2 4 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 162 260 (accept_3_2 7 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162
  260 2 3 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  162 260 (Polychromatic418967fa.accept_19_5_10_13_1_4883 5 162 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 162 260 2 2 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 162 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 162 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 260 2 1 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 260 (accept_3_2 1 162 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  161 260 (Eq.refl Bool.true) (allA_succ_of_accept 99 161 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 161 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 161 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 98 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 161 260 (accept_3_2 97 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 161 260 (Polychromatic418967fa.accept_15_6_11_5_1_168 96 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 161 260 (Polychromatic418967fa.accept_18_5_17_8_1_2984 95 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 161 260 (accept_3_2 94 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 161 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 161 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 161 260
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 92 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 161 260 (accept_3_2 91 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 161 260 (Polychromatic418967fa.accept_14_6_7_8_1_624 90 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 161 260 (Polychromatic418967fa.accept_21_5_14_8_1_6818 89 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 161 260 (accept_3_2 88 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 161 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 161 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 161 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 86 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 161 260 (accept_3_2 85 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 161 260 (Polychromatic418967fa.accept_15_9_11_5_1_1283 84 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 161 260 (Polychromatic418967fa.accept_14_13_7_8_1_677 83 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 161 260 (accept_3_2 82 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 161 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 161 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 161 260
  (Polychromatic418967fa.accept_17_12_8_5_1_6018 80 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 161 260 (accept_3_2 79 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 161 260 (Polychromatic418967fa.accept_16_14_1_4_1_5432 78 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 161 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 77 161 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 161 260 (accept_3_2 76 161 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 161 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 161 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 74 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 161 260 (accept_3_2 73 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 161 260 (Polychromatic418967fa.accept_16_8_1_4_1_6622 72 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 161 260 (Polychromatic418967fa.accept_14_1_7_8_1_2063 71 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 161 260 (accept_3_2 70 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 161 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 161 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 161 260
  (Polychromatic418967fa.accept_15_8_11_5_1_169 68 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 161 260 (accept_3_2 67 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 161 260 (Polychromatic418967fa.accept_15_6_11_5_1_168 66 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 161 260 (Polychromatic418967fa.accept_21_2_14_8_1_6834 65 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 260 (accept_3_2 64 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 161 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 161 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 161 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 62 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 161 260 (accept_3_2 61 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 161 260 (Polychromatic418967fa.accept_16_12_1_4_1_5403 60 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 161 260 (Polychromatic418967fa.accept_18_5_17_8_1_2984 59 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 260 (accept_3_2 58 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 161 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 161 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 161 260
  (Polychromatic418967fa.accept_16_8_1_4_1_6622 56 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 161 260 (accept_3_2 55 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 161 260 (Polychromatic418967fa.accept_15_9_11_5_1_1283 54 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 161 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 161 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 260 (accept_3_2 52 161 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 161 260 (accept_3_2 49 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 161 260 (Polychromatic418967fa.accept_14_6_7_8_1_624 48 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 161 260 (Polychromatic418967fa.accept_15_2_11_5_1_1266 47 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 260 (accept_3_2 46 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 161 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 260
  (Polychromatic418967fa.accept_16_12_1_4_1_5403 44 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 161 260 (accept_3_2 43 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 161 260 (Polychromatic418967fa.accept_19_4_9_13_1_7792 42 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 161 260 (Polychromatic418967fa.accept_14_13_7_8_1_677 41 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 260 (accept_3_2 40 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 161 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 260 (accept_3_2 37 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 260 (Polychromatic418967fa.accept_15_6_11_5_1_168 36 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 161 260 (Polychromatic418967fa.accept_16_3_1_4_1_5426 35 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 260 (accept_3_2 34 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 161 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 260
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 32 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 260 (accept_3_2 31 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 260 (Polychromatic418967fa.accept_16_14_1_4_1_5432 30 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 161 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 260 (accept_3_2 28 161 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 260 (accept_3_2 25 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 260 (Polychromatic418967fa.accept_15_9_11_5_1_1283 24 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 260 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 260 (accept_3_2 22 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 161 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 260
  (Polychromatic418967fa.accept_14_6_7_8_1_624 20 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 260 (accept_3_2 19 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 260 (Polychromatic418967fa.accept_19_18_9_13_1_3496 18 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 260 (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 260 (accept_3_2 16 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 161 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 260 (accept_3_2 13 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 260 (Polychromatic418967fa.accept_16_12_1_4_1_5403 12 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 260 (Polychromatic418967fa.accept_21_11_14_8_1_5256 11 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 260 (accept_3_2 10 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 161 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 260
  (Polychromatic418967fa.accept_15_8_11_5_1_169 8 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 260 (accept_3_2 7 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 260 (Polychromatic418967fa.accept_14_6_7_8_1_624 6 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 161 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 260 (accept_3_2 4 161 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 161 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 260 (accept_3_2 1 161 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 160 260 (Eq.refl Bool.true) (allA_of_3_0 101 160 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 102 159
  260 (Eq.refl Bool.true) (allA_succ_of_accept 101 159 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 101 159 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 159 260 (accept_3_2 100 159 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 159 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 99
  159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 159 260
  (Polychromatic418967fa.accept_19_3_7_13_1_2338 98 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 159 260 (accept_3_2 97 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 159 260 (Polychromatic418967fa.accept_17_11_6_5_1_3662 96 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 159 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 159 260 (accept_3_2 94 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 159 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 159 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 159 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 92 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 159 260 (accept_3_2 91 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 159 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 90 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 159 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 159 260 (accept_3_2 88 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 159 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 159 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 159 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 86 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 159 260 (accept_3_2 85 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 159 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 159 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 159 260 (accept_3_2 82 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 159 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 159 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 159 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 80 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 159 260 (accept_3_2 79 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 159 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 159 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 159 260 (accept_3_2 76 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 159 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 159 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 159 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 74 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 159 260 (accept_3_2 73 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 159 260 (Polychromatic418967fa.accept_15_12_9_5_1_2973 72 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 159 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 159 260 (accept_3_2 70 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 159 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 159 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 159 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 159 260 (accept_3_2 67 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 159 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 159 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 159 260 (accept_3_2 64 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 159 260 (Polychromatic418967fa.accept_15_3_9_5_1_2082 63 159 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 159 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 62 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 159 260 (accept_3_2 61 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 159 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 159 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 260 (accept_3_2 58 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 159 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 159 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 159 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 159 260 (accept_3_2 55 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 159 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 159 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 260 (accept_3_2 52 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 159 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 159 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 159 260 (accept_3_2 49 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 159 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 159 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 260 (accept_3_2 46 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 159 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 159 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 260
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 44 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 159 260 (accept_3_2 43 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 159 260 (Polychromatic418967fa.accept_11_9_5_7_1_815 42 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 159 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 260 (accept_3_2 40 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 159 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 159 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 159 260 (accept_3_2 37 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 159 260 (Polychromatic418967fa.accept_19_17_7_13_1_4833 36 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 159 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 260 (accept_3_2 34 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 260 (Polychromatic418967fa.accept_15_3_9_5_1_2082 33 159 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 159 260 (accept_3_2 31 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 159 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 159 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 260 (accept_3_2 28 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 159 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 159 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 260
  (Polychromatic418967fa.accept_15_11_9_5_1_2974 26 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 159 260 (accept_3_2 25 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 159 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 159 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 260 (accept_3_2 22 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 159 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 260 (accept_3_2 19 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 159 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 159 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 260 (accept_3_2 16 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 260 (Polychromatic418967fa.accept_19_15_7_13_1_11844 15 159 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 260 (accept_3_2 13 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 159 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 159 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 260 (accept_3_2 10 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 260 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 159 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 260
  (Polychromatic418967fa.accept_16_8_15_4_1_5402 8 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 260 (accept_3_2 7 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  159 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 159 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 260 (accept_3_2 4 159 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 159 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 260 (accept_3_2 1 159 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 158 260 (Eq.refl Bool.true) (allA_succ_of_gcd 102 158 260 2 51 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 158 260 (Polychromatic418967fa.accept_7_3_4_1_1_71
  101 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 158 260 2 50 79 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 158 260
  (Polychromatic418967fa.accept_19_4_6_13_1_6335 99 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 158 260 2 49 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 158 260 (accept_3_2 97 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 158 260 2 48 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 158 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 95 158 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 158 260 2 47 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 158 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 93 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 158 260 2 46 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 158 260 (accept_3_2 91 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 158 260 2 45 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 158 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 89 158 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 158 260 2 44 79 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 158 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 87 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 158 260 2 43 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 158 260 (accept_3_2 85 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 158 260 2 42 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 158 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 158 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 158 260 2 41 79 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 158 260
  (Polychromatic418967fa.accept_14_11_4_8_1_664 81 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 158 260 2 40 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 158 260 (accept_3_2 79 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 158 260 2 39 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 158 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 158 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 158 260 2 38 79 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 158 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 75 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 158 260 2 37 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 158 260 (accept_3_2 73 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 158 260 2 36 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 158 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 158 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 158 260 2 35 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 158 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 69 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 158 260 2 34 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 158 260 (accept_3_2 67 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 158 260 2 33 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 158 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 158 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 158 260 2 32 79 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 158 260
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 63 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 158 260 2 31 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 158 260 (accept_3_2 61 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 158 260 2 30 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 158 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 158 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 158 260 2 29 79 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 158 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 158 260 2 28 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 158 260 (accept_3_2 55 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 158 260 2 27 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 158 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 158 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 158 260 2 26 79 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 158 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 158 260 2 25 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 158 260 (accept_3_2 49 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 158 260 2 24 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 158 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 158 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 260 2 23 79 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 158 260 2 22 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 158 260 (accept_3_2 43 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 260 2 21 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 260 (Polychromatic418967fa.accept_11_8_4_7_1_1303 41 158 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 260 2 20 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 260 2 19 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 260 (accept_3_2 37 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 260 2 18 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 158 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 260 2 17 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 260 2 16 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 260 (accept_3_2 31 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 260 2 15 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 158 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 260 2 14 79 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 260
  (Polychromatic418967fa.accept_15_12_8_5_1_5048 27 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 260 2 13 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 260 (accept_3_2 25 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 260 2 12 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 158 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 260 2 11 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 260 2 10 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 260 (accept_3_2 19 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 260 2 9 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 158 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 260 2 8 79 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 260 2 7 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 158 260 (accept_3_2 13 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 260 2 6 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 158 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 260 2 5 79 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 260
  (Polychromatic418967fa.accept_16_9_14_4_1_3225 9 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 260 2 4 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 260 (accept_3_2 7 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  260 2 3 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 158 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 260 2 2 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 158 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 260 2 1 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 260 (accept_3_2 1 158 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 157 260 (Eq.refl Bool.true) (allA_of_3_0 104 157 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 105 156
  260 (Eq.refl Bool.true) (allA_succ_of_gcd 104 156 260 52 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 156 260 (accept_3_2 103 156 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 156 260 2 51 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 156 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 101 156 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 156 260 4 25 39 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 156 260
  (Polychromatic418967fa.accept_14_1_2_8_1_655 99 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 156 260 2 49 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 156 260 (accept_3_2 97 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 156 260 4 24 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 156 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 95 156 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 156 260 2 47 78 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 156 260
  (Polychromatic418967fa.accept_15_3_6_5_1_2079 93 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 156 260 4 23 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 91 156 260 13 7 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 156 260 2 45 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 156 260 (Polychromatic418967fa.accept_15_14_6_5_1_7215 89 156
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 156 260 4 22 39 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 156 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 87 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 156 260 2 43 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 156 260 (accept_3_2 85 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 156 260 4 21 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 156 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 156 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 156 260 2 41 78 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 156 260
  (Polychromatic418967fa.accept_16_1_12_4_1_695 81 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 156 260 4 20 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 156 260 (accept_3_2 79 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 156 260 26 3 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 156 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 156 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 156 260 4 19 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 156 260 (Polychromatic418967fa.accept_11_9_2_7_1_1298
  75 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 156 260 2 37 78 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 156 260
  (accept_3_2 73 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 156 260 4 18 39 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 156 260
  (Polychromatic418967fa.accept_14_1_2_8_1_655 71 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 156 260 2 35 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 156 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 156 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 156 260 4 17 39 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 156 260 (accept_3_2 67 156 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 156 260 2 33 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 156 260 13 5 12 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 156 260 4 16 39 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 156 260
  (Polychromatic418967fa.accept_15_3_6_5_1_2079 63 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 156 260 2 31 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 156 260 (accept_3_2 61 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 260 4 15 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 156 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 156 260 2 29 78 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 156 260
  (Polychromatic418967fa.accept_14_1_2_8_1_655 57 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 156 260 4 14 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 156 260 (accept_3_2 55 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 260 2 27 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 260 (Polychromatic418967fa.accept_11_9_2_7_1_1298 53 156 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 156 260 52 1 3 5 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 156 260
  (Polychromatic418967fa.accept_9_6_3_8_1_595 51 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 156 260 2 25 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 156 260 (accept_3_2 49 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 260 4 12 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 156 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 156 260 2 23 78 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 156 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 156 260 4 11 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 156 260 (accept_3_2 43 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 260 2 21 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 156 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 260 4 10 39 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 156 260 13 3 12 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 156 260 2 19 78 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 260 (accept_3_2 37
  156 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 156 260 4 9 39 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 156 260
  (Polychromatic418967fa.accept_16_3_12_4_1_170 35 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 156 260 2 17 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 156 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 156 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 156 260 4 8 39 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 260 (accept_3_2 31 156 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 156 260 2 15 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 29
  156 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 260 4 7 39 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 156 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 156 260 26 1 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 156 260 (accept_3_2 25 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24
  156 260 4 6 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  23 156 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 156 260 2 11 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 156 260 (Polychromatic418967fa.accept_16_5_12_4_1_4325 21 156 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 156 260 4 5 39 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 260 (accept_3_2 19 156 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 260 2 9 78 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 156 260 4 4 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 156 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 156 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 156 260 2 7 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 13 156 260 13 1 12 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 156 260 4 3 39 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 156 260 2 5 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 156 260 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 156 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 156 260 4 2 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 260 (accept_3_2 7 156 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 260 2 3 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 156 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 260 4 1 39 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 156 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 156 260 2 1 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 156 260 (accept_3_2 1 156 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 155 260 (Eq.refl Bool.true) (allA_succ_of_gcd 105 155 260 5 21 31 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 155 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 104 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 155 260 (accept_3_2 103 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 155 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 102 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 155 260 (Polychromatic418967fa.accept_17_16_2_5_1_6031 101 155 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 155 260 5 20 31 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 155 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 99 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 155 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 98 155 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 155 260 (accept_3_2 97 155 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 155 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 96 155 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 155 260 5 19 31 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 155 260 (accept_3_2 94 155 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 155 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 155 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 155 260
  (Polychromatic418967fa.accept_16_12_11_4_1_1359 92 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 155 260 (accept_3_2 91 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 155 260 5 18 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 155 260 (Polychromatic418967fa.accept_16_9_11_4_1_3194 89 155 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 155 260 (accept_3_2 88 155 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 155 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 155 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 155 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 155 260 5 17 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 84 155 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 155 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 155 260 (Polychromatic418967fa.accept_11_6_1_7_1_1315
  83 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 155 260 (accept_3_2 82
  155 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 155 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 81 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 155 260 5 16 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 155 260 (accept_3_2 79 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 155 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 155 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 155 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 155 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 155 260 (accept_3_2 76 155 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 155 260 5 15 31 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 155 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 74 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 155 260 (accept_3_2 73 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 155 260 (Polychromatic418967fa.accept_11_6_1_7_1_1315 72 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 155 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 71 155 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 155 260 5 14 31 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 155 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 69 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 155 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 155 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 155 260 (accept_3_2 67 155 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 155 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 155 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 155 260 5 13 31 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 155 260 (accept_3_2 64 155 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 155 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 155 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 155 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 62 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 155 260 (accept_3_2 61 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60
  155 260 5 12 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 155 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 155 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 155 260 (accept_3_2 58 155 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 155 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 155 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 155 260
  (Polychromatic418967fa.accept_16_8_11_4_1_3290 56 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 155 260 5 11 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 155 260 (Polychromatic418967fa.accept_16_6_11_4_1_635 54 155 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 260
  (Polychromatic418967fa.accept_25_3_5_10_1_15878 53 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 155 260 (accept_3_2 52 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 155 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 155 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 155 260 5 10 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 155 260 (accept_3_2 49 155 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 155 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 155 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 260
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 155 260 (accept_3_2 46 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  155 260 5 9 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 155 260 (Polychromatic418967fa.accept_14_2_1_8_1_650 44 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 155 260 (accept_3_2 43 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 155 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 155 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 155 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 155 260 5 8 31 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 155 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 155 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 155 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 260 (accept_3_2 37 155 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 155 260 (Polychromatic418967fa.accept_22_14_1_18_1_1901 36 155 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 155 260 5 7 31 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 155 260 (accept_3_2 34 155 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 155 260 (accept_3_2 31 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  155 260 5 6 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 155 260 (Polychromatic418967fa.accept_19_10_3_13_1_6284 29 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 155 260 (accept_3_2 28 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 155 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 155 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 155
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 155 260 5 5 31 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 155 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 24 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 155 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 155 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 260 (accept_3_2 22 155 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 155 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 155 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 155 260 5 4 31 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 155 260 (accept_3_2 19 155 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 260 (Polychromatic418967fa.accept_25_18_5_10_1_15877 18
  155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 260
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 260 (accept_3_2 16 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  155 260 5 3 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 155 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 155 260 (accept_3_2 13 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 155 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 155 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 260 (Polychromatic418967fa.accept_19_11_3_13_1_9178 11 155
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 155 260 5 2 31 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 155 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 155 260 (Polychromatic418967fa.accept_16_8_11_4_1_3290 8 155 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 260 (accept_3_2 7 155 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 155 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 155 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 155 260 5 1 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 155 260 (accept_3_2 4 155 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 155 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 260 (accept_3_2 1 155 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 154 260 (Eq.refl Bool.true) (allA_of_3_0 107 154 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 108 153 260 (Eq.refl Bool.true) (allA_succ_of_accept 107 153 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 153 260 (accept_3_2 106 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 153 260 (Polychromatic418967fa.accept_14_7_13_8_1_2067 105 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 153 260 (Polychromatic418967fa.accept_16_8_9_4_1_630 104 153 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 153 260 (accept_3_2 103 153 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 153 260
  (Polychromatic418967fa.accept_11_3_10_7_1_129 102 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 153 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 101 153 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 153 260 (accept_3_2 100 153 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 153 260 (Polychromatic418967fa.accept_15_9_3_5_1_2077 99 153 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 153 260
  (Polychromatic418967fa.accept_15_8_3_5_1_608 98 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 153 260 (accept_3_2 97 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 153 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 96 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 153 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 153 260 (accept_3_2 94 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 153 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 153 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 153 260
  (Polychromatic418967fa.accept_15_2_3_5_1_2991 92 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 153 260 (accept_3_2 91 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 153 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 153 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 153 260 (accept_3_2 88 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 153 260 (Polychromatic418967fa.accept_21_3_6_8_1_11449 87 153 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 153 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 86 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 153 260 (accept_3_2 85 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 153 260 (Polychromatic418967fa.accept_15_9_3_5_1_2077 84 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 153 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 153 260 (accept_3_2 82 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 153 260 (Polychromatic418967fa.accept_15_6_3_5_1_607 81 153 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 153 260
  (Polychromatic418967fa.accept_11_3_10_7_1_129 80 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 153 260 (accept_3_2 79 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 153 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 153 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 260 (accept_3_2 76 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 153 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 153 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 153 260
  (Polychromatic418967fa.accept_23_5_15_7_1_15876 74 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 153 260 (accept_3_2 73 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 153 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 153 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 153 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 153 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 260 (accept_3_2 70 153 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 153 260 (Polychromatic418967fa.accept_8_5_1_4_1_628
  69 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 153 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 68 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 153 260 (accept_3_2 67 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 153 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 153 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 260 (accept_3_2 64 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 260 (Polychromatic418967fa.accept_14_7_13_8_1_2067 63 153 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 153 260
  (Polychromatic418967fa.accept_15_2_3_5_1_2991 62 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 153 260 (accept_3_2 61 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 153 260 (Polychromatic418967fa.accept_16_12_9_4_1_4345 60 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 153 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 260 (accept_3_2 58 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 260 (Polychromatic418967fa.accept_18_3_9_8_1_2977 57 153 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 260
  (Polychromatic418967fa.accept_16_8_9_4_1_630 56 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 153 260 (accept_3_2 55 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 153 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 153 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 260 (accept_3_2 52 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 153 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 260
  (Polychromatic418967fa.accept_19_12_1_13_1_11823 50 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 153 260 (accept_3_2 49 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 153 260 (Polychromatic418967fa.accept_19_10_1_13_1_11824 48 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 153 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 47
  153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 260 (accept_3_2 46
  153 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 260
  (Polychromatic418967fa.accept_8_5_1_4_1_628 45 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 153 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 153 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 260 (accept_3_2 43 153 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 153 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 153 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 153 260 (accept_3_2 40 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 153 260 (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 153 260 (Polychromatic418967fa.accept_15_8_3_5_1_608 38 153 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 260 (accept_3_2 37 153 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 260 (Polychromatic418967fa.accept_11_3_10_7_1_129 36 153
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 153 260 (accept_3_2 34 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 153 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 153 260 (Polychromatic418967fa.accept_15_2_3_5_1_2991 32 153 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 260 (accept_3_2 31 153 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 153 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 260 (accept_3_2 28 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 153 260 (Polychromatic418967fa.accept_16_11_9_4_1_5438 27 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 153 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 260 (accept_3_2 25 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 260 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 153 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 260 (accept_3_2 22 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 153 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 260 (Polychromatic418967fa.accept_23_20_15_7_1_15875 20 153 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 260 (accept_3_2 19 153 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 153
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 260 (accept_3_2 16 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 153 260 (Polychromatic418967fa.accept_21_15_6_8_1_9888 15 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 153 260 (Polychromatic418967fa.accept_11_3_10_7_1_129 14 153 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 260 (accept_3_2 13 153 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 153 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 260 (accept_3_2 10 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  153 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 153 260 (Polychromatic418967fa.accept_15_8_3_5_1_608 8 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 260 (accept_3_2 7 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 153 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 260 (accept_3_2 4 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 260 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 153 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 260 (accept_3_2 1 153 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 153
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 152 260 (Eq.refl Bool.true) (allA_succ_of_gcd 108 152 260 4 27 38 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 152 260
  (Polychromatic418967fa.accept_16_11_8_4_1_2234 107 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 152 260 2 53 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 105 152 260 (Polychromatic418967fa.accept_16_9_8_4_1_1354 105 152 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 152 260 4 26 38 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 152 260 (accept_3_2
  103 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 152 260 2 51 76 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 152 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 101 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 152 260 4 25 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 152 260 (Polychromatic418967fa.accept_16_3_8_4_1_3279 99 152 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 152 260 2 49 76 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 152 260 (accept_3_2 97 152 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 152 260 4 24 38 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 152 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 95 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 152 260 2 47 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 152 260 (Polychromatic418967fa.accept_11_5_9_7_1_411 93 152 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 152 260 4 23 38 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 152 260 (accept_3_2 91 152 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 152 260 2 45 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 152 260 (Polychromatic418967fa.accept_15_14_2_5_1_1272
  89 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 152 260 4 22 38 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 152 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 87 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 152 260 2 43 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 152 260 (accept_3_2 85 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 152 260 4 21 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 152 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 152 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 152 260 2 41 76 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 152 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 81 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 152 260 4 20 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 152 260 (accept_3_2 79 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 152 260 2 39 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 152 260 (Polychromatic418967fa.accept_16_13_8_4_1_3250 77 152 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 152 260 4 19 38 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 152 260
  (Polychromatic418967fa.accept_16_11_8_4_1_2234 75 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 152 260 2 37 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 152 260 (accept_3_2 73 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 152 260 4 18 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 152 260 (Polychromatic418967fa.accept_11_5_9_7_1_411 71 152 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 152 260 2 35 76 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 152 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 69 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 152 260 4 17 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 152 260 (accept_3_2 67 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 152 260 2 33 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 152 260 (Polychromatic418967fa.accept_16_1_8_4_1_4334 65 152 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 152 260 4 16 38 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 152 260
  (Polychromatic418967fa.accept_15_3_2_5_1_2980 63 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 152 260 2 31 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 152 260 (accept_3_2 61 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 152 260 4 15 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 152 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 152 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 152 260 2 29 76 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 152 260
  (Polychromatic418967fa.accept_11_2_9_7_1_124 57 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 152 260 4 14 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 152 260 (accept_3_2 55 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 152 260 2 27 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 152 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 152 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 260 4 13 38 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 260
  (Polychromatic418967fa.accept_16_3_8_4_1_3279 51 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 152 260 2 25 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 152 260 (accept_3_2 49 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 152 260 4 12 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 152 260 (Polychromatic418967fa.accept_16_15_8_4_1_1355 47 152 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 152 260 2 23 76 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 152 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 152 260 4 11 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 152 260 (accept_3_2 43 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 152 260 2 21 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 152 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 152 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 260 4 10 38 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 260 2 19 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 152 260 (accept_3_2 37 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 152 260 4 9 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 152 260 (Polychromatic418967fa.accept_11_2_9_7_1_124 35 152 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 260 2 17 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 260 (Polychromatic418967fa.accept_15_3_2_5_1_2980
  33 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 152 260 4 8 38 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 152 260
  (accept_3_2 31 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 152 260 2 15 76 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 152 260
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 152 260 4 7 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 152 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 152 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 152 260 2 13 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 152 260 (accept_3_2 25 152 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 152 260 4 6 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 152 260 (Polychromatic418967fa.accept_16_7_8_4_1_689 23 152 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 260 2 11 76 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 260
  (Polychromatic418967fa.accept_16_5_8_4_1_5418 21 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 260 4 5 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 152 260 (accept_3_2 19 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  152 260 2 9 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 152 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 152 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 260 4 4 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 260 (Polychromatic418967fa.accept_16_15_8_4_1_1355
  15 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 260 2 7 76 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 260
  (accept_3_2 13 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 260 4 3 38 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 152 260 2 5 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 152 260 (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 152 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 152 260 4 2 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 152 260 (accept_3_2 7 152 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152 260 2 3 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 152 260 (Polychromatic418967fa.accept_11_5_9_7_1_411 5 152 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 152 260 4 1 38 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 152 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 152 260 2 1 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 152 260 (accept_3_2 1 152 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 151 260 (Eq.refl Bool.true) (allA_of_3_0 110 151 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 111 150 260 (Eq.refl Bool.true) (allA_succ_of_gcd 110 150 260 10 11 15 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 150 260 (accept_3_2 109 150 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 150 260 2 54 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 150 260 (Polychromatic418967fa.accept_7_2_3_1_1_10
  107 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 150 260 2 53 75 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 150 260 5 21 30
  52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 150 260 2 52
  75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 150
  260 (accept_3_2 103 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 150 260 2 51 75 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 150 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 101 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 150 260 10 10 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 150 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 99 150 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 150 260 2 49 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 150 260 (accept_3_2 97 150 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 150 260 2 48 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 150 260 5 19 30 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 94 150 260 2 47 75 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 150 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 93 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 150 260 2 46 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 150 260 (accept_3_2 91 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 150 260 10 9 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 150 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 150 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 150 260 2 44 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 150 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 87 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 150 260 2 43 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 85 150 260 5 17 30 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 150 260 2 42 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 150 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 83 150 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 150 260 2 41 75 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 150 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 81 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 150 260 10 8 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 150 260 (accept_3_2 79 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 150 260 2 39 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 150 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 150 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 150 260 2 38 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 150 260 5 15 30 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 150 260 2 37 75 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 150 260 (accept_3_2 73
  150 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 150 260 2 36 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 150 260
  (Polychromatic418967fa.accept_23_2_12_7_1_15840 71 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 150 260 10 7 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 150 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 69 150 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 150 260 2 34 75 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 150 260 (accept_3_2 67 150 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 150 260 2 33 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 150 260 5 13 30 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 150 260 2 32 75 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 150 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 150 260 2 31 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 150 260 (accept_3_2 61 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 260 10 6 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 150 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 150 260 2 29 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 150 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 150 260 2 28 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 150 260 5 11 30 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 150 260 2 27 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 150 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 150 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 150 260 2 26 75 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 150 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 150 260 10 5 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 150 260 (accept_3_2 49 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 260 2 24 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 150 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 260 2 23 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 150 260 5 9 30 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 150 260 2 22 75 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 260 (accept_3_2 43 150 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 150 260 2 21 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 150 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 150 260 10 4 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 150 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 150 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 150 260 2 19 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 260 (accept_3_2 37 150 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 150 260 2 18 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 150 260 5 7 30 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 150 260 2 17 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 150 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 150 260 2 16 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 150 260 (accept_3_2 31 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 260 10 3 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 150 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 260 2 14 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 150 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 150 260 2 13 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 150 260 5 5 30 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 150 260 2 12 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 150 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 150 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 260 2 11 75 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 260 10 2 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 260 (accept_3_2 19 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 260 2 9 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 150 260 (Polychromatic418967fa.accept_21_17_3_8_1_6793 17 150 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 260 2 8 75 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 150 260 5 3 30 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 150 260 2 7 75 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 260 (accept_3_2 13
  150 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 260 2 6 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 150 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 260 10 1 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 150 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 150 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 150 260 2 4 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 260 (accept_3_2 7 150 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 260 2 3 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 150 260 5 1 30 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 150 260 2 2 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 150 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  150 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 260 2 1 75 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 260 (accept_3_2 1
  150 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 149 260 (Eq.refl Bool.true) (allA_succ_of_accept 111 149 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 111 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 149 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 110 149 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 149 260 (accept_3_2 109 149 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 149 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 108 149 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 149 260
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 107 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 149 260 (accept_3_2 106 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 149 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 149 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 104 149
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 149 260 (accept_3_2 103 149
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 149 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 102 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 149 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 101 149 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 149 260 (accept_3_2 100 149 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 149 260 (Polychromatic418967fa.accept_12_2_5_8_1_159
  98 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 149 260 (accept_3_2 97
  149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 149 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 96 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 149 260 (Polychromatic418967fa.accept_16_15_5_4_1_6678 95 149 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 149 260 (accept_3_2 94 149 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 149 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 92
  149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 149 260 (accept_3_2 91
  149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 149 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 90 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 149 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 89 149 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 149 260 (accept_3_2 88 149 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 149 260 (Polychromatic418967fa.accept_12_2_5_8_1_159
  86 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 149 260 (accept_3_2 85
  149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 149 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 84 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 149 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 149 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 149 260 (accept_3_2 82 149 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 149 260 (Polychromatic418967fa.accept_7_3_2_1_1_225
  80 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 149 260 (accept_3_2 79
  149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 149 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 78 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 149 260 (Polychromatic418967fa.accept_15_2_14_5_1_2072 77 149 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 149 260 (accept_3_2 76 149 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 149 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 74
  149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 149 260 (accept_3_2 73
  149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 149 260
  (Polychromatic418967fa.accept_16_8_5_4_1_674 72 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 149 260 (Polychromatic418967fa.accept_14_1_9_8_1_2863 71 149 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 149 260 (accept_3_2 70 149 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 149 260
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 68 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 149 260 (accept_3_2 67 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 149 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 149 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 65 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 149 260 (accept_3_2 64 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 149 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 149 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 62 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 149 260 (accept_3_2 61 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 149 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 149 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 149 260 (accept_3_2 58 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 149 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 149 260 (accept_3_2 55 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 149 260 (Polychromatic418967fa.accept_15_9_14_5_1_2086 54 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 149 260 (Polychromatic418967fa.accept_15_8_14_5_1_2089 53 149 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 260 (accept_3_2 52 149 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 149 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 149 260 (accept_3_2 49 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 149 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 149 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 260 (accept_3_2 46 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 149 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 260
  (Polychromatic418967fa.accept_16_12_5_4_1_3275 44 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 149 260 (accept_3_2 43 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 149 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 149 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 260 (accept_3_2 40 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 149 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 260 (accept_3_2 37 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 260 (Polychromatic418967fa.accept_15_6_14_5_1_2976 36 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 149 260 (Polychromatic418967fa.accept_18_17_5_8_1_1898 35 149 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 260 (accept_3_2 34 149 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 149 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 260
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 32 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 149 260 (accept_3_2 31 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 149 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 149 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 260 (accept_3_2 28 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 149 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 260 (accept_3_2 25 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 260 (Polychromatic418967fa.accept_11_1_6_7_1_116 23 149 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 260 (accept_3_2 22 149 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 149 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 260 (accept_3_2 19 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 260 (Polychromatic418967fa.accept_19_18_16_13_1_10572 18 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 149 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 260 (accept_3_2 16 149 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 149 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 260 (accept_3_2 13 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 260 (accept_3_2 10 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 149 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 260
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 260 (accept_3_2 7 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 260 (Polychromatic418967fa.accept_21_5_2_8_1_5267 5 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 260 (accept_3_2 4 149 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 149 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 260 (accept_3_2 1 149 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 148 260 (Eq.refl Bool.true) (allA_of_3_0 113 148 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 114 147 260 (Eq.refl Bool.true) (allA_succ_of_accept 113 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 147 260 (accept_3_2 112 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 147 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 111 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 147 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 110 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 147 260 (accept_3_2 109 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 147 260 (Polychromatic418967fa.accept_16_12_3_4_1_4317 108
  147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 147 260 (accept_3_2 106 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 147 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 105 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 147 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 104 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 147 260 (accept_3_2 103 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 147 260 (Polychromatic418967fa.accept_11_3_4_7_1_114 102 147
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 147 260 (accept_3_2 100 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 147 260 (Polychromatic418967fa.accept_14_1_7_8_1_2063 99 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 147 260 (Polychromatic418967fa.accept_15_8_12_5_1_2987 98 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 147 260 (accept_3_2 97 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 147 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 96 147 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 147 260 (accept_3_2 94 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 147 260 (Polychromatic418967fa.accept_28_9_7_8_1_15874 93 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 147 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 92 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 147 260 (accept_3_2 91 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 147 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 147 260 (accept_3_2 88 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 147 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 147 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 86 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 147 260 (accept_3_2 85 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 147 260 (Polychromatic418967fa.accept_15_9_12_5_1_1267 84 147 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 147 260 (accept_3_2 82 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 147 260 (Polychromatic418967fa.accept_15_6_12_5_1_2108 81 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 147 260 (Polychromatic418967fa.accept_11_3_4_7_1_114 80 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 147 260 (accept_3_2 79 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 147 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 147 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 147 260 (accept_3_2 76 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 147 260 (Polychromatic418967fa.accept_17_7_11_5_1_3539 75 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 147 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 74 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 260 (accept_3_2 73 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 147 260 (Polychromatic418967fa.accept_16_8_3_4_1_3233 72 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 147 260 (accept_3_2 70 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 147 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 147 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 68 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 260 (accept_3_2 67 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 147 260 (accept_3_2 64 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 147 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 147 260 (Polychromatic418967fa.accept_14_6_7_8_1_624 62 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 260 (accept_3_2 61 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 147 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 147 260 (accept_3_2 58 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 147 260 (Polychromatic418967fa.accept_14_1_7_8_1_2063 57 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 147 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 260 (accept_3_2 55 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 147 260 (accept_3_2 52 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 147 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 147 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 260 (accept_3_2 49 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 260 (Polychromatic418967fa.accept_14_6_7_8_1_624 48 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 260 (accept_3_2 46 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 147 260 (Polychromatic418967fa.accept_18_9_3_8_1_5419 45 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 147 260 (Polychromatic418967fa.accept_16_12_3_4_1_4317 44 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 260 (accept_3_2 43 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 147 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 260 (accept_3_2 40 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 147 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 147 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 260 (accept_3_2 37 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 260 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 260 (accept_3_2 34 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 147 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 147 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 260 (accept_3_2 31 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 260 (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 260 (accept_3_2 28 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 147 260 (Polychromatic418967fa.accept_14_13_7_8_1_677 27 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 260 (Polychromatic418967fa.accept_25_1_22_10_1_3339 26 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 260 (accept_3_2 25 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 147 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 260 (accept_3_2 22 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 147 260 (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 147 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 260 (accept_3_2 19 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 260 (accept_3_2 16 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 147 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 147 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 260 (accept_3_2 13 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 260 (Polychromatic418967fa.accept_16_12_3_4_1_4317 12 147 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 260 (accept_3_2 10 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 260 (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 260 (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 260 (accept_3_2 7 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 147 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 260 (accept_3_2 4 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 260 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 147 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 260 (accept_3_2 1 147 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 115 146 260 (Eq.refl Bool.true) (allA_succ_of_gcd 114 146 260 2 57 73 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 146 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 113 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 146 260 2 56 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 146 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 111 146 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 146 260 2 55 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 146 260 (accept_3_2 109 146 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 146 260 2 54 73 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 146 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 107 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 146 260 2 53 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 146 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 105 146 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 146 260 2 52 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 146 260 (accept_3_2 103 146 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 146 260 2 51 73 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 146 260
  (Polychromatic418967fa.accept_12_5_2_8_1_172 101 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 146 260 2 50 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 146 260 (Polychromatic418967fa.accept_15_9_11_5_1_1283 99 146 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 146 260 2 49 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 146 260 (accept_3_2 97 146 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 146 260 2 48 73 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 146 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 95 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 146 260 2 47 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 146 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 146 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 146 260 2 46 73 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 146 260 (accept_3_2 91 146 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 146 260 2 45 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 146 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 89
  146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 146 260 2 44 73 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 146 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 87 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 146 260 2 43 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 146 260 (accept_3_2 85 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 146 260 2 42 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 146 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 146 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 146 260 2 41 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 146 260
  (Polychromatic418967fa.accept_11_4_3_7_1_828 81 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 146 260 2 40 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 146 260 (accept_3_2 79 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 146 260 2 39 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 146 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 146 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 146 260 2 38 73 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 146 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 75 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 146 260 2 37 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 146 260 (accept_3_2 73 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 146 260 2 36 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 146 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 146 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 146 260 2 35 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 146 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 69 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 146 260 2 34 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 146 260 (accept_3_2 67 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 146 260 2 33 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 146 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 146 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 146 260 2 32 73 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 146 260
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 63 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 146 260 2 31 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 146 260 (accept_3_2 61 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 146 260 2 30 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 146 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 146 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 146 260 2 29 73 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 146 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 146 260 2 28 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 146 260 (accept_3_2 55 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 146 260 2 27 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 146 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 146 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 146 260 2 26 73 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 146 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 146 260 2 25 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 146 260 (accept_3_2 49 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 146 260 2 24 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 146 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 146 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 260 2 23 73 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 260
  (Polychromatic418967fa.accept_22_1_14_18_1_15873 45 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 146 260 2 22 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 146 260 (accept_3_2 43 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 260 2 21 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 146 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 260 2 20 73 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 260 2 19 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 260 (accept_3_2 37 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 260 2 18 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 146 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 260 2 17 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 260 2 16 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 260 (accept_3_2 31 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 260 2 15 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 146 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 260 2 14 73 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 260
  (Polychromatic418967fa.accept_23_4_8_7_1_15872 27 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 260 2 13 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 260 (accept_3_2 25 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 260 2 12 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 146 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 260 2 11 73 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 260 2 10 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 260 (accept_3_2 19 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 260 2 9 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 146 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 260 2 8 73 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 260 2 7 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 146 260 (accept_3_2 13 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 260 2 6 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 146 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 146 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 260 2 5 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 260 2 4 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 260 (accept_3_2 7 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  260 2 3 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 146 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 260 2 2 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 146 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 146 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 260 2 1 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 260 (accept_3_2 1 146 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 145 260 (Eq.refl Bool.true) (allA_of_3_0 116 145 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 117 144 260 (Eq.refl Bool.true) (allA_succ_of_gcd 116 144 260 4 29 36 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 144 260 (accept_3_2 115 144 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 144 260 2 57 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 144 260
  (Polychromatic418967fa.accept_25_13_19_10_1_3337 113 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 112 144 260 4 28 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 111 144 260 (Polychromatic418967fa.accept_19_16_11_13_1_4944 111 144 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 144 260 2 55 72 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 144 260 (accept_3_2
  109 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 144 260 4 27 36 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 144 260
  (Polychromatic418967fa.accept_19_12_11_13_1_4885 107 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 144 260 2 53 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 105 144 260 (Polychromatic418967fa.accept_11_6_1_7_1_1315 105 144 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 144 260 4 26 36 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 144 260 (accept_3_2
  103 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 144 260 2 51 72 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 144 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 101 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 144 260 4 25 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 144 260 (Polychromatic418967fa.accept_21_15_18_8_1_6809 99 144 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 144 260 2 49 72 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 144 260 (accept_3_2 97 144 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 144 260 4 24 36 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 144 260
  (Polychromatic418967fa.accept_14_11_4_8_1_664 95 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 144 260 2 47 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 144 260 (Polychromatic418967fa.accept_15_3_9_5_1_2082 93 144 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 144 260 4 23 36 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 144 260 (accept_3_2 91 144 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 144 260 2 45 72 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 144 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 89 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 144 260 4 22 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 144 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 144 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 144 260 2 43 72 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 144 260 (accept_3_2 85 144 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 144 260 4 21 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 144 260 (Polychromatic418967fa.accept_11_6_1_7_1_1315
  83 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 144 260 2 41 72 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 144 260
  (Polychromatic418967fa.accept_14_11_4_8_1_664 81 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 144 260 4 20 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 144 260 (accept_3_2 79 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 144 260 2 39 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 144 260 (Polychromatic418967fa.accept_22_11_12_18_1_15871 77 144 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 144 260 4 19 36 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 144 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 75 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 144 260 2 37 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 144 260 (accept_3_2 73 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 144 260 4 18 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 144 260 (Polychromatic418967fa.accept_15_11_9_5_1_2974 71 144 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 144 260 2 35 72 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 144 260
  (Polychromatic418967fa.accept_19_12_11_13_1_4885 69 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 144 260 4 17 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 144 260 (accept_3_2 67 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 144 260 2 33 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 144 260 (Polychromatic418967fa.accept_25_15_19_10_1_12421 65 144 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 144 260 4 16 36 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 144 260
  (Polychromatic418967fa.accept_15_3_9_5_1_2082 63 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 144 260 2 31 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 144 260 (accept_3_2 61 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 260 4 15 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 144 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 260 2 29 72 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 144 260
  (Polychromatic418967fa.accept_15_12_9_5_1_2973 57 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 144 260 4 14 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 144 260 (accept_3_2 55 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 260 2 27 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 144 260 (Polychromatic418967fa.accept_14_11_4_8_1_664 53 144 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 260 4 13 36 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 144 260
  (Polychromatic418967fa.accept_21_9_18_8_1_11475 51 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 144 260 2 25 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 144 260 (accept_3_2 49 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 260 4 12 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 144 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 144 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 144 260 2 23 72 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 144 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 144 260 4 11 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 144 260 (accept_3_2 43 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 260 2 21 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 144 260 (Polychromatic418967fa.accept_15_11_9_5_1_2974 41 144 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 260 4 10 36 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 144 260
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 144 260 2 19 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 144 260 (accept_3_2 37 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 260 4 9 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 144 260 (Polychromatic418967fa.accept_19_16_11_13_1_4944 35 144 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 260 2 17 72 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 144 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 144 260 4 8 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 144 260 (accept_3_2 31 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  144 260 2 15 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 144 260 (Polychromatic418967fa.accept_15_14_9_5_1_3932 29 144 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 260 4 7 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 260 (Polychromatic418967fa.accept_15_12_9_5_1_2973
  27 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 144 260 2 13 72 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 260
  (accept_3_2 25 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 144 260 4 6 36 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 144 260
  (Polychromatic418967fa.accept_25_23_19_10_1_12420 23 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 144 260 2 11 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 144 260 (Polychromatic418967fa.accept_19_2_11_13_1_9180 21 144 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 144 260 4 5 36 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 260 (accept_3_2 19
  144 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 260 2 9 72 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 144 260 4 4 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 144 260 (Polychromatic418967fa.accept_21_15_18_8_1_6809 15 144 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 260 2 7 72 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 260 (accept_3_2 13 144 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 260 4 3 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 260 (Polychromatic418967fa.accept_14_11_4_8_1_664
  11 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 260 2 5 72 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 144 260
  (Polychromatic418967fa.accept_21_9_18_8_1_11475 9 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 144 260 4 2 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 260 (accept_3_2 7 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144
  260 2 3 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  144 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 144 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 144 260 4 1 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 144 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 144 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 260 2 1 72 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 260 (accept_3_2 1 144 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 118 143 260 (Eq.refl Bool.true) (allA_succ_of_gcd 117 143 260 13 9 11 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 143 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 116 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 143 260 (accept_3_2 115 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 143 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 114 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 143 260 (Polychromatic418967fa.accept_17_11_7_5_1_1567 113 143 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 143 260 (accept_3_2 112 143 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 143 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 143
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 143 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 110 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 143 260 (accept_3_2 109 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 143 260 (Polychromatic418967fa.accept_15_3_8_5_1_2105 108 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 143 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 107 143 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 143 260 (accept_3_2 106 143 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 143 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 143
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 143 260 13 8 11 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 143 260 (accept_3_2
  103 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 143 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 102 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 143 260 (Polychromatic418967fa.accept_15_11_8_5_1_1278 101 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 143 260 (accept_3_2 100 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 143 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 143 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 143 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 98 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 143 260 (accept_3_2 97 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 143 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 96 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 143 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 95 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 143 260 (accept_3_2 94 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 143 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 143 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 143 260
  (Polychromatic418967fa.accept_16_12_15_4_1_5422 92 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 91 143 260 13 7 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 90 143 260 (Polychromatic418967fa.accept_23_21_5_7_1_12638 90 143 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 143 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 89 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 143 260 (accept_3_2 88 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 143 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 143 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 86 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 143 260 (accept_3_2 85 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 143 260 (Polychromatic418967fa.accept_23_15_5_7_1_15870 84 143 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 143 260
  (Polychromatic418967fa.accept_8_3_7_4_1_42 83 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 143 260 (accept_3_2 82 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 143 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 143 260 (Polychromatic418967fa.accept_17_12_7_5_1_8659 80 143 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 143 260 (accept_3_2 79 143 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 143 260 13 6 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 143 260 (Polychromatic418967fa.accept_17_9_7_5_1_1566
  77 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 143 260 (accept_3_2 76
  143 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 143 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 75 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 143 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 74 143 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 143 260 (accept_3_2 73 143 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 143 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 143 260
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 71 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 143 260 (accept_3_2 70 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 143 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 143 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 143 260 (accept_3_2 67 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 143 260 (Polychromatic418967fa.accept_17_15_7_5_1_9836 66 143 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 143 260 13 5 11 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 143 260 (accept_3_2 64
  143 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 143 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 143 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 143 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 143 260 (accept_3_2 61 143 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 143 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 143 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 59
  143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 143 260 (accept_3_2 58
  143 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 143 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 57 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 143 260 (Polychromatic418967fa.accept_15_11_8_5_1_1278 56 143 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 143 260 (accept_3_2 55 143 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 143 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 53
  143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 143 260 13 4 11 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 143 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 51 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 143 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 143 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 143 260 (accept_3_2 49 143 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 143 260 (Polychromatic418967fa.accept_15_3_8_5_1_2105 48 143 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 143 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 143 260 (accept_3_2 46 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 143 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 143 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 143 260 (accept_3_2 43 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 143 260 (Polychromatic418967fa.accept_15_12_8_5_1_5048 42 143 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 260
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 41 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 143 260 (accept_3_2 40 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39
  143 260 13 3 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 143 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 143 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 260 (accept_3_2 37 143 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 143 260 (Polychromatic418967fa.accept_21_15_17_8_1_9937 36 143 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 260
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 260 (accept_3_2 34 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 260 (accept_3_2 31 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 143 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 260
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 29 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 260 (accept_3_2 28 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 143 260 13 2 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 143 260 (accept_3_2 25 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 143 260 (Polychromatic418967fa.accept_16_8_15_4_1_5402 24 143 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 143 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 260 (accept_3_2 22 143 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 260
  (Polychromatic418967fa.accept_18_2_17_8_1_1893 20 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 143 260 (accept_3_2 19 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 143 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 143 260 (Polychromatic418967fa.accept_22_17_11_18_1_15869 17 143 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 260 (accept_3_2 16 143 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 143 260 13 1 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 12 143 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 11
  143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 260 (accept_3_2 10
  143 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 143 260 (Polychromatic418967fa.accept_16_8_15_4_1_5402 8 143 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 260 (accept_3_2 7 143 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 143 260 (Polychromatic418967fa.accept_19_6_10_13_1_4839 6 143 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 260 (accept_3_2 4 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 260 (accept_3_2 1 143 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 142 260 (Eq.refl Bool.true) (allA_of_3_0 119 142 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 120 141 260 (Eq.refl Bool.true) (allA_succ_of_accept 119 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 141 260 (accept_3_2 118 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 141 260 (Polychromatic418967fa.accept_15_12_6_5_1_1275 117 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 116 141 260 (Polychromatic418967fa.accept_15_11_6_5_1_1295 116 141 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 141 260 (accept_3_2 115 141 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 141 260 (Polychromatic418967fa.accept_12_6_9_8_1_165
  114 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 141 260 (accept_3_2 112 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 141 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 111 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 141 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 110 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 141 260 (accept_3_2 109 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 141 260 (Polychromatic418967fa.accept_15_3_6_5_1_2079 108 141
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 141 260 (accept_3_2 106 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 141 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 105 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 141 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 104 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 141 260 (accept_3_2 103 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 141 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 102 141
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 141 260 (accept_3_2 100 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 141 260 (Polychromatic418967fa.accept_19_4_8_13_1_7802 99 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 141 260 (Polychromatic418967fa.accept_19_3_8_13_1_13229 98 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 141 260 (accept_3_2 97 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 141 260 (Polychromatic418967fa.accept_19_1_8_13_1_4875 96 141
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 141 260 (accept_3_2 94 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 141 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 141 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 92 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 141 260 (accept_3_2 91 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 141 260 (Polychromatic418967fa.accept_11_2_9_7_1_124 90 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 141 260 (accept_3_2 88 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 141 260 (Polychromatic418967fa.accept_15_12_6_5_1_1275 87 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 141 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 86 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 260 (accept_3_2 85 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 141 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 141 260 (accept_3_2 82 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 141 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 81 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 141 260 (Polychromatic418967fa.accept_19_4_8_13_1_7802 80 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 260 (accept_3_2 79 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 141 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 141
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 141 260 (accept_3_2 76 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 141 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 141 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 74 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 260 (accept_3_2 73 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 260 (Polychromatic418967fa.accept_14_2_1_8_1_650 72 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 141 260 (accept_3_2 70 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 141 260 (Polychromatic418967fa.accept_21_6_15_8_1_9895 69 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 141 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 68 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 260 (accept_3_2 67 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 141 260 (accept_3_2 64 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 141 260 (Polychromatic418967fa.accept_14_7_1_8_1_2873 63 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 141 260 (Polychromatic418967fa.accept_19_5_8_13_1_9161 62 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 260 (accept_3_2 61 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 260 (Polychromatic418967fa.accept_11_5_9_7_1_411 60 141
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 141 260 (accept_3_2 58 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 141 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 141 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 260 (accept_3_2 55 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 141 260 (accept_3_2 52 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 141 260 (Polychromatic418967fa.accept_14_9_1_8_1_2849 51 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 141 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 260 (accept_3_2 49 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 260 (accept_3_2 46 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 141 260 (Polychromatic418967fa.accept_21_3_15_8_1_12962 45 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 141 260 (Polychromatic418967fa.accept_14_2_1_8_1_650 44 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 260 (accept_3_2 43 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 141
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 260 (accept_3_2 40 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 141 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 141 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 260 (accept_3_2 37 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 260 (Polychromatic418967fa.accept_27_9_6_17_1_15868 36 141 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 260 (accept_3_2 34 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 141 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 141 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 260 (accept_3_2 31 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 260 (accept_3_2 28 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 141 260 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 141 260 (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 260 (accept_3_2 25 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 260 (Polychromatic418967fa.accept_11_2_9_7_1_124 24 141
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 260 (accept_3_2 22 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 260 (accept_3_2 19 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 260 (accept_3_2 16 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 260 (Polychromatic418967fa.accept_22_15_9_18_1_15867 15 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 260 (accept_3_2 13 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 141 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 260 (accept_3_2 10 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 260 (Polychromatic418967fa.accept_16_8_13_4_1_3258 8 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 260 (accept_3_2 7 141 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 141 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 260 (accept_3_2 4 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 141 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 260 (accept_3_2 1 141 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 121 140 260 (Eq.refl Bool.true) (allA_succ_of_gcd 120 140 260 20 6 7 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 140 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 119 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 140 260 2 59 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 140 260 (Polychromatic418967fa.accept_16_5_12_4_1_4325 117 140 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 140 260 4 29 35 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 115 140 260 5 23 28 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 114 140 260 2 57 70 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 140 260
  (Polychromatic418967fa.accept_16_1_12_4_1_695 113 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 140 260 4 28 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 140 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 111 140 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 140 260 10 11 14 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 140 260 (accept_3_2 109 140 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 140 260 4 27 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 140 260
  (Polychromatic418967fa.accept_16_11_12_4_1_3195 107 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 140 260 2 53 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 105 140 260 5 21 28 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 140 260 4 26 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 140 260 (accept_3_2 103 140 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 102 140 260 2 51 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 140 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 101 140 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 140 260 20 5 7 13 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 140 260
  (Polychromatic418967fa.accept_16_3_12_4_1_170 99 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 140 260 2 49 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 140 260 (accept_3_2 97 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 140 260 4 24 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 95 140 260 5 19 28 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 94 140 260 2 47 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 140 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 93 140 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 140 260 4 23 35 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 140 260 (accept_3_2 91
  140 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 140 260 10 9 14 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 140 260
  (Polychromatic418967fa.accept_16_9_12_4_1_3255 89 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 140 260 4 22 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 140 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 87 140 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 140 260 2 43 70 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 85 140 260 5 17 28 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 140 260 4 21 35 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 140 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 140 260 2 41 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 140 260 (Polychromatic418967fa.accept_11_4_8_7_1_819 81 140 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 140 260 20 4 7 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 140 260 (accept_3_2 79 140 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 140 260 2 39 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 140 260
  (Polychromatic418967fa.accept_16_13_12_4_1_4323 77 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 140 260 4 19 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 75 140 260 5 15 28 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 140 260 2 37 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 140 260 (accept_3_2 73 140 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 140 260 4 18 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 140 260 (Polychromatic418967fa.accept_16_7_12_4_1_1347 71 140
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 140 260 10 7 14 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 140 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 69 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 140 260 4 17 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 140 260 (accept_3_2 67 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 140 260 2 33 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 140 260 5 13 28 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 140 260 4 16 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 140 260 (Polychromatic418967fa.accept_16_15_12_4_1_4324 63 140
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 140 260 2 31 70 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 140 260 (accept_3_2 61
  140 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 140 260 20 3 7 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 140 260
  (Polychromatic418967fa.accept_11_4_8_7_1_819 59 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 140 260 2 29 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 140 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 140 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 140 260 4 14 35 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 140 260 5 11 28 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 140 260 2 27 70 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 140 260
  (Polychromatic418967fa.accept_16_5_12_4_1_4325 53 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 140 260 4 13 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 140 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 140 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 140 260 10 5 14 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 140 260 (accept_3_2 49 140 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 140 260 4 12 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 140 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 47
  140 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 140 260 2 23 70 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 140 260 5 9 28 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 140 260 4 11 35 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 140 260
  (accept_3_2 43 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 140 260 2 21 70 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 140 260
  (Polychromatic418967fa.accept_16_9_12_4_1_3255 41 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 140 260 20 2 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 140 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 140 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 140 260 2 19 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 140 260 (accept_3_2 37 140 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 140 260 4 9 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 140 260 5 7 28 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 140 260 2 17 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 33
  140 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 140 260 4 8 35 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 140 260 (accept_3_2 31
  140 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 140 260 10 3 14 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 140 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 140 260 4 7 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 140 260 (Polychromatic418967fa.accept_16_11_12_4_1_3195 27 140 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 140 260 2 13 70 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 140 260 5 5 28 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 140 260 4 6 35 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 140 260
  (Polychromatic418967fa.accept_16_7_12_4_1_1347 23 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 140 260 2 11 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 140 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 140 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 140 260 20 1 7 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 140 260 (accept_3_2 19 140 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 140 260 2 9 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 140 260 (Polychromatic418967fa.accept_16_1_12_4_1_695
  17 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 260 4 4 35 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 140 260 5 3 28 52
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 140 260 2 7 70
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 260
  (accept_3_2 13 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 260 4 3 35 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 140 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 140 260 10 1 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 140 260 (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 140 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 260 4 2 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 140 260 (accept_3_2 7 140 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140 260 2 3 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 140 260 5 1 28 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 140 260 4 1 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 140 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 260 2 1 70 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 260 (accept_3_2 1
  140 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 122 139 260 (Eq.refl Bool.true) (allA_of_3_0 122 139 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 123 138 260 (Eq.refl Bool.true) (allA_succ_of_gcd 122 138 260 2 61 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 138 260 (accept_3_2 121 138 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 138 260 2 60 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 138 260 (Polychromatic418967fa.accept_9_2_3_8_1_318
  119 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 138 260 2 59 69 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 138 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 117 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 138 260 2 58 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 138 260 (accept_3_2 115 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 138 260 2 57 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 138 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 113 138 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 138 260 2 56 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 138 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 111 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 138 260 2 55 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 138 260 (accept_3_2 109 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 138 260 2 54 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 138 260 (Polychromatic418967fa.accept_15_2_3_5_1_2991 107 138 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 138 260 2 53 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 138 260
  (Polychromatic418967fa.accept_9_6_3_8_1_595 105 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 138 260 2 52 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 138 260 (accept_3_2 103 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 138 260 2 51 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 138 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 101 138 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 138 260 2 50 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 138 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 99 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 138 260 2 49 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 138 260 (accept_3_2 97 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 138 260 2 48 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 138 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 95 138 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 138 260 2 47 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 138 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 93 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 138 260 2 46 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 138 260 (accept_3_2 91 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 138 260 2 45 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 138 260 (Polychromatic418967fa.accept_11_1_6_7_1_116 89 138 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 138 260 2 44 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 138 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 87 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 138 260 2 43 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 138 260 (accept_3_2 85 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 138 260 2 42 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 138 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 138 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 138 260 2 41 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 138 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 81 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 138 260 2 40 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 138 260 (accept_3_2 79 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 138 260 2 39 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 138 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 138 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 138 260 2 38 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 138 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 75 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 138 260 2 37 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 138 260 (accept_3_2 73 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 260 2 36 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 260 (Polychromatic418967fa.accept_17_3_2_5_1_2556 71 138 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 138 260 2 35 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 138 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 69 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 138 260 2 34 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 138 260 (accept_3_2 67 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 260 2 33 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 138 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 138 260 2 32 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 138 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 138 260 2 31 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 138 260 (accept_3_2 61 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 260 2 30 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 138 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 138 260 2 29 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 138 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 138 260 2 28 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 138 260 (accept_3_2 55 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 260 2 27 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 138 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 138 260 2 26 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 138 260
  (Polychromatic418967fa.accept_9_6_3_8_1_595 51 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 138 260 2 25 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 138 260 (accept_3_2 49 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 260 2 24 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 138 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 260 2 23 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 138 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 138 260 2 22 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 138 260 (accept_3_2 43 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 260 2 21 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 138 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 260 2 20 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 138 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 138 260 2 19 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 138 260 (accept_3_2 37 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 260 2 18 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 260 (Polychromatic418967fa.accept_21_14_12_8_1_6833 35 138 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 260 2 17 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 138 260
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 138 260 2 16 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 138 260 (accept_3_2 31 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 260 2 15 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 138 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 260 2 14 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 138 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 138 260 2 13 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 138 260 (accept_3_2 25 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 260 2 12 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 138 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 260 2 11 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 138 260 2 10 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 138 260 (accept_3_2 19 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 260 2 9 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 138 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 138 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 260 2 8 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 138 260
  (Polychromatic418967fa.accept_9_6_3_8_1_595 15 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 138 260 2 7 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 138 260 (accept_3_2 13 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 260 2 6 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 138 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 138 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 260 2 5 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 260 2 4 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 260 (accept_3_2 7 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138
  260 2 3 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  138 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 138 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 260 2 2 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 138 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 138 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 260 2 1 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 260 (accept_3_2 1 138 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 124 137 260 (Eq.refl Bool.true) (allA_succ_of_accept 123 137 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 123 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 137 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 122 137 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 137 260 (accept_3_2 121 137 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 137 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 120 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 137 260
  (Polychromatic418967fa.accept_11_9_5_7_1_815 119 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 137 260 (accept_3_2 118 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 137 260 (Polychromatic418967fa.accept_14_4_11_8_1_2034 116 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 137 260 (accept_3_2 115 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 137 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 114 137
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 137 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 113 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 137 260 (accept_3_2 112 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 137 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 110 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 137 260 (accept_3_2 109 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 137 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 108 137
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 137 260
  (Polychromatic418967fa.accept_16_11_9_4_1_5438 107 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 137 260 (accept_3_2 106 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 137 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 137 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 104 137
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 137 260 (accept_3_2 103 137
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 137 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 102 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 137 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 101 137 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 137 260 (accept_3_2 100 137 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 137 260 (Polychromatic418967fa.accept_12_2_5_8_1_159
  98 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 137 260 (accept_3_2 97
  137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 137 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 96 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 137 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 137 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 137 260 (accept_3_2 94 137 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 137 260
  (Polychromatic418967fa.accept_16_12_9_4_1_4345 92 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 137 260 (accept_3_2 91 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 137 260 (Polychromatic418967fa.accept_19_14_4_13_1_7779 90 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 137 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 89 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 137 260 (accept_3_2 88 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 137 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 137 260 (accept_3_2 85 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 137 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 137 260 (Polychromatic418967fa.accept_19_7_4_13_1_6319 83 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 137 260 (accept_3_2 82 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 137 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 137 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 80 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 137 260 (accept_3_2 79 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 137 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 137 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 77 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 137 260 (accept_3_2 76 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 137 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 74 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 137 260 (accept_3_2 73 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 137 260 (Polychromatic418967fa.accept_15_12_2_5_1_3939 72 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 137 260 (Polychromatic418967fa.accept_15_11_2_5_1_2076 71 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 137 260 (accept_3_2 70 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 137 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 137 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 68 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 137 260 (accept_3_2 67 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 137 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 137 260 (Polychromatic418967fa.accept_19_8_4_13_1_4912 65 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 137 260 (accept_3_2 64 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 137 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 137 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 62 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 137 260 (accept_3_2 61 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 137 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 137 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 137 260 (accept_3_2 58 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 137 260
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 56 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 137 260 (accept_3_2 55 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 137 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 137 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 260 (accept_3_2 52 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 137 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 137 260 (accept_3_2 49 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 137 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 137 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 260 (accept_3_2 46 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 260
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 44 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 137 260 (accept_3_2 43 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 137 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 260 (accept_3_2 40 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 137 260 (accept_3_2 37 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 137 260 (Polychromatic418967fa.accept_19_17_4_13_1_4828 36 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 260 (Polychromatic418967fa.accept_21_14_11_8_1_5272 35 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 260 (accept_3_2 34 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 137 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 260 (accept_3_2 31 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 260 (accept_3_2 28 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 260 (accept_3_2 25 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 260 (accept_3_2 22 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 260
  (Polychromatic418967fa.accept_11_9_5_7_1_815 20 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 260 (accept_3_2 19 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 260 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 260 (accept_3_2 16 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 260 (accept_3_2 13 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 260 (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 260 (accept_3_2 10 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 137 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 260
  (Polychromatic418967fa.accept_16_8_9_4_1_630 8 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 260 (accept_3_2 7 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 260 (accept_3_2 4 137 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 137 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 260 (accept_3_2 1 137 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 125 136 260 (Eq.refl Bool.true) (allA_of_3_0 125 136 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 126 135 260 (Eq.refl Bool.true) (allA_succ_of_gcd 125 135 260 5 25 27 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 124 135 260 (accept_3_2 124 135 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 135 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 123 135
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 135 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 122 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 135 260 (accept_3_2 121 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  120 135 260 5 24 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 119 135 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 119 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 135 260 (accept_3_2 118 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 135 260 (Polychromatic418967fa.accept_21_12_9_8_1_2370 117 135 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 135 260
  (Polychromatic418967fa.accept_22_6_3_18_1_8074 116 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 115 135 260 5 23 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 114 135 260 (Polychromatic418967fa.accept_11_4_3_7_1_828 114 135 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 135 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 135 260 (accept_3_2 112 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 135 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 111 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 110 135 260 5 22 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 135 260 (accept_3_2 109 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 135 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 108 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 135 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 107 135
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 135 260 (accept_3_2 106 135
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 135 260 5 21 27 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 135 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 104 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 135 260 (accept_3_2 103 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 135 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 102 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 135 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 101 135 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 135 260 5 20 27 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 135 260
  (Polychromatic418967fa.accept_8_3_7_4_1_42 99 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 135 260 (Polychromatic418967fa.accept_11_10_3_7_1_2564 98 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 135 260 (accept_3_2 97 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 135 260 (Polychromatic418967fa.accept_17_11_16_5_1_3612 96 135 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 135 260 5 19 27 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 135 260 (accept_3_2 94 135 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 135 260
  (Polychromatic418967fa.accept_16_13_7_4_1_3248 93 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 135 260 (Polychromatic418967fa.accept_11_4_3_7_1_828 92 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 135 260 (accept_3_2 91 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 135 260 5 18 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 135 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 135 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 135 260 (accept_3_2 88 135 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 135 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 135 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 135 260
  (Polychromatic418967fa.accept_17_1_16_5_1_3670 86 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 135 260 5 17 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 84 135 260 (Polychromatic418967fa.accept_19_8_2_13_1_2328 84 135 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 135 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 135 260 (accept_3_2 82 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 135 260 (Polychromatic418967fa.accept_11_4_3_7_1_828 81 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 135 260 5 16 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 135 260 (accept_3_2 79 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 135 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 135 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 260 (accept_3_2 76 135 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 135 260 5 15 27 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 135 260
  (Polychromatic418967fa.accept_29_16_19_28_1_15866 74 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 135 260 (accept_3_2 73 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 135 260 (Polychromatic418967fa.accept_16_8_7_4_1_2217 72 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 135 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 135 260 5 14 27 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 135 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 135 260 (Polychromatic418967fa.accept_19_11_2_13_1_4907 68 135 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 260 (accept_3_2 67 135 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 135 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 135 260 5 13 27 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 135 260 (accept_3_2 64 135 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 135 260
  (Polychromatic418967fa.accept_19_6_2_13_1_4945 63 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 135 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 260 (accept_3_2 61 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 135 260 5 12 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 135 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 135 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 260 (accept_3_2 58 135 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 260 (Polychromatic418967fa.accept_14_1_9_8_1_2863 57 135
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 260
  (Polychromatic418967fa.accept_16_8_7_4_1_2217 56 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 135 260 5 11 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 135 260 (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 135 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 135 260 (accept_3_2 52 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 135 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 135 260 5 10 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 135 260 (accept_3_2 49 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 135 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 135 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 260 (accept_3_2 46 135 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 135 260 5 9 27 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 135 260
  (Polychromatic418967fa.accept_16_12_7_4_1_687 44 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 135 260 (accept_3_2 43 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 135 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 135 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 135 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 135 260 5 8 27 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 135 260
  (Polychromatic418967fa.accept_18_3_9_8_1_2977 39 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 135 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 260 (accept_3_2 37 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 135 260 (Polychromatic418967fa.accept_17_2_16_5_1_1584 36 135 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 135 260 5 7 27 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 135 260 (accept_3_2 34 135 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 260
  (Polychromatic418967fa.accept_21_12_9_8_1_2370 33 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 135 260 (Polychromatic418967fa.accept_11_10_3_7_1_2564 32 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 260 (accept_3_2 31 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 135 260 5 6 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 135 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 135 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 260 (accept_3_2 28 135 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 135 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 260
  (Polychromatic418967fa.accept_11_4_3_7_1_828 26 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 135 260 5 5 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 135 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 260 (accept_3_2 22 135 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 260
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 135 260 5 4 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 135 260 (accept_3_2 19 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 135 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 135 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 135 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 260 (accept_3_2 16 135 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 260 5 3 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 260 (Polychromatic418967fa.accept_16_14_7_4_1_3243 14 135
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 260 (accept_3_2 13 135
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 260
  (Polychromatic418967fa.accept_16_12_7_4_1_687 12 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 135 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 135 260 5 2 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 135 260 (Polychromatic418967fa.accept_22_9_3_18_1_11251
  9 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 260
  (Polychromatic418967fa.accept_16_8_7_4_1_2217 8 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 260 (accept_3_2 7 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  135 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 135 260 5 1 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 135 260 (accept_3_2 4 135 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 135 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 135 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 260 (Polychromatic418967fa.accept_17_2_16_5_1_1584 2 135
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 260 (accept_3_2 1 135 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 127 134 260 (Eq.refl Bool.true) (allA_succ_of_gcd 126 134 260 2 63 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 134 260
  (Polychromatic418967fa.accept_12_5_2_8_1_172 125 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 134 260 2 62 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 134 260 (Polychromatic418967fa.accept_16_11_6_4_1_2228 123 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 134 260 2 61 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 134 260 (accept_3_2 121 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 134 260 2 60 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 134 260
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 119 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 134 260 2 59 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 134 260 (Polychromatic418967fa.accept_16_5_6_4_1_3211 117 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 134 260 2 58 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 134 260 (accept_3_2 115 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 134 260 2 57 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 134 260
  (Polychromatic418967fa.accept_12_5_2_8_1_172 113 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 134 260 2 56 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 134 260 (Polychromatic418967fa.accept_15_6_14_5_1_2976 111 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 134 260 2 55 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 134 260 (accept_3_2 109 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 134 260 2 54 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 134 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 107 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 134 260 2 53 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 134 260 (Polychromatic418967fa.accept_19_10_1_13_1_11824 105 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 134 260 2 52 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 134 260 (accept_3_2 103 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 134 260 2 51 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 134 260
  (Polychromatic418967fa.accept_12_5_2_8_1_172 101 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 134 260 2 50 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 134 260 (Polychromatic418967fa.accept_15_9_14_5_1_2086 99 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 134 260 2 49 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 134 260 (accept_3_2 97 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 134 260 2 48 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 134 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 95 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 134 260 2 47 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 134 260 (Polychromatic418967fa.accept_16_13_6_4_1_3277 93 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 134 260 2 46 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 134 260 (accept_3_2 91 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 134 260 2 45 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 134 260
  (Polychromatic418967fa.accept_12_5_2_8_1_172 89 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 134 260 2 44 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 134 260 (Polychromatic418967fa.accept_28_3_22_8_1_15865 87 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 134 260 2 43 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 134 260 (accept_3_2 85 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 134 260 2 42 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 134 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 83 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 134 260 2 41 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 134 260 (Polychromatic418967fa.accept_15_6_14_5_1_2976 81 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 134 260 2 40 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 134 260 (accept_3_2 79 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 134 260 2 39 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 134 260
  (Polychromatic418967fa.accept_12_5_2_8_1_172 77 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 134 260 2 38 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 134 260 (Polychromatic418967fa.accept_11_9_2_7_1_1298 75 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 134 260 2 37 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 134 260 (accept_3_2 73 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 134 260 2 36 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 134 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 71 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 134 260 2 35 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 134 260 (Polychromatic418967fa.accept_15_9_14_5_1_2086 69 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 134 260 2 34 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 134 260 (accept_3_2 67 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 134 260 2 33 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 134 260
  (Polychromatic418967fa.accept_12_5_2_8_1_172 65 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 134 260 2 32 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 134 260 (Polychromatic418967fa.accept_25_13_9_10_1_12456 63 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 134 260 2 31 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 134 260 (accept_3_2 61 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 134 260 2 30 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 134 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 59 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 134 260 2 29 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 134 260 (Polychromatic418967fa.accept_22_13_2_18_1_4747 57 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 134 260 2 28 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 134 260 (accept_3_2 55 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 134 260 2 27 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 134 260
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 53 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 134 260 2 26 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 134 260 (Polychromatic418967fa.accept_15_6_14_5_1_2976 51 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 134 260 2 25 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 134 260 (accept_3_2 49 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 134 260 2 24 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 134 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 47 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 134 260 2 23 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 134 260 (Polychromatic418967fa.accept_16_13_6_4_1_3277 45 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 134 260 2 22 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 134 260 (accept_3_2 43 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 134 260 2 21 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 134 260
  (Polychromatic418967fa.accept_12_5_2_8_1_172 41 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 134 260 2 20 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 134 260 (Polychromatic418967fa.accept_15_9_14_5_1_2086 39 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 134 260 2 19 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 134 260 (accept_3_2 37 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 134 260 2 18 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 134 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 35 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 134 260 2 17 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 134 260 (Polychromatic418967fa.accept_19_14_1_13_1_7810 33 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 134 260 2 16 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 134 260 (accept_3_2 31 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 134 260 2 15 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 134 260
  (Polychromatic418967fa.accept_12_5_2_8_1_172 29 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 134 260 2 14 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 134 260 (Polychromatic418967fa.accept_16_11_6_4_1_2228 27 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 134 260 2 13 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 134 260 (accept_3_2 25 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 134 260 2 12 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 134 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 134 260 2 11 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 134 260 (Polychromatic418967fa.accept_15_6_14_5_1_2976 21 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 134 260 2 10 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 134 260 (accept_3_2 19 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 134 260 2 9 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 134 260
  (Polychromatic418967fa.accept_12_5_2_8_1_172 17 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 134 260 2 8 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 134 260 (Polychromatic418967fa.accept_25_15_9_10_1_15864 15 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 134 260 2 7 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 134 260 (accept_3_2 13 134 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 134 260 2 6 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 134 260
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 134 260 2 5 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 134 260 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 134 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 134 260 2 4 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 134 260 (accept_3_2 7 134 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134 260 2 3 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 134 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 5
  134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 134 260 2 2 67 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 134 260
  (Polychromatic418967fa.accept_16_3_6_4_1_679 3 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 134 260 2 1 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 134 260 (accept_3_2 1 134 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 128 133 260 (Eq.refl Bool.true) (allA_of_3_0 128 133 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 129 132 260 (Eq.refl Bool.true) (allA_succ_of_gcd 128 132 260 4 32 33 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 132 260 (accept_3_2 127 132 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 132 260 2 63 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 132 260
  (Polychromatic418967fa.accept_23_10_17_7_1_5931 125 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 124 132 260 4 31 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 123 132 260 (Polychromatic418967fa.accept_19_9_18_13_1_4931 123 132 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 132 260 2 61 66 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 132 260 (accept_3_2
  121 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 132 260 4 30 33 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 132 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 119 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 132 260 2 59 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 132 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 117 132 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 132 260 4 29 33 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 132 260 (accept_3_2 115 132 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 132 260 2 57 66 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 132 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 113 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 132 260 4 28 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 132 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 111 132 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 132 260 2 55 66 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 132 260 (accept_3_2 109 132 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 132 260 4 27 33 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 132 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 107 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 132 260 2 53 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 132 260 (Polychromatic418967fa.accept_14_7_6_8_1_2856 105 132 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 132 260 4 26 33 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 132 260 (accept_3_2 103 132 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 132 260 2 51 66 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 132 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 101 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 132 260 4 25 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 132 260 (Polychromatic418967fa.accept_15_9_12_5_1_1267 99 132 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 132 260 2 49 66 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 132 260 (accept_3_2 97 132 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 132 260 4 24 33 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 132 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 95 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 132 260 2 47 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 132 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 132 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 132 260 4 23 33 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 132 260 (accept_3_2 91 132 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 132 260 2 45 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 132 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 89
  132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 132 260 4 22 33 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 132 260
  (Polychromatic418967fa.accept_21_3_6_8_1_11449 87 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 132 260 2 43 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 132 260 (accept_3_2 85 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 132 260 4 21 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 132 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 83 132 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 132 260 2 41 66 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 132 260
  (Polychromatic418967fa.accept_15_6_12_5_1_2108 81 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 132 260 4 20 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 132 260 (accept_3_2 79 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 260 2 39 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 132 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 132 260 4 19 33 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 132 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 75 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 132 260 2 37 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 132 260 (accept_3_2 73 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 260 4 18 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 260 (Polychromatic418967fa.accept_19_14_18_13_1_7823 71 132 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 132 260 2 35 66 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 132 260
  (Polychromatic418967fa.accept_15_9_12_5_1_1267 69 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 132 260 4 17 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 132 260 (accept_3_2 67 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 260 2 33 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 132 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 132 260 4 16 33 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 132 260
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 63 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 132 260 2 31 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 132 260 (accept_3_2 61 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 260 4 15 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 132 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 132 260 2 29 66 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 132 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 132 260 4 14 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 132 260 (accept_3_2 55 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 260 2 27 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 260 (Polychromatic418967fa.accept_15_8_12_5_1_2987 53 132 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 132 260 4 13 33 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 132 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 132 260 2 25 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 132 260 (accept_3_2 49 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 260 4 12 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 132 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 132 260 2 23 66 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 132 260
  (Polychromatic418967fa.accept_18_9_6_8_1_2989 45 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 132 260 4 11 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 132 260 (accept_3_2 43 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 260 2 21 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 132 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 260 4 10 33 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 132 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 132 260 2 19 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 132 260 (accept_3_2 37 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 260 4 9 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 132 260 (Polychromatic418967fa.accept_14_7_6_8_1_2856 35 132 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 260 2 17 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 132 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 33
  132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 132 260 4 8 33 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 260 (accept_3_2 31
  132 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 260 2 15 66 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 260 4 7 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 132 260 (Polychromatic418967fa.accept_17_10_13_5_1_3513 27 132 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 260 2 13 66 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 260 (accept_3_2 25 132 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 260 4 6 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 23
  132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 260 2 11 66 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 132 260 4 5 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 132 260 (accept_3_2 19 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  132 260 2 9 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 260 (Polychromatic418967fa.accept_15_2_12_5_1_2107 17 132 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 260 4 4 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 260
  (Polychromatic418967fa.accept_17_15_13_5_1_9877 15 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 132 260 2 7 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 132 260 (accept_3_2 13 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 260 4 3 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 132 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 132 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 260 2 5 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 9
  132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 132 260 4 2 33 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 260 (accept_3_2 7
  132 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 260 2 3 66 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 132 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 132 260 4 1 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 132 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 132 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 260 2 1 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 260 (accept_3_2 1 132 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 132
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 130 131 260 (Eq.refl Bool.true) (allA_succ_of_accept 129 131 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 129 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 131 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 128 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 131 260 (accept_3_2 127 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 131 260 (Polychromatic418967fa.accept_15_6_11_5_1_168 126 131 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 131 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 125 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 131 260 (accept_3_2 124 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 123 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 131 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 122 131 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 131 260 (accept_3_2 121 131 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 131 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 120 131
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 131 260
  (Polychromatic418967fa.accept_8_7_3_4_1_404 119 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 131 260 (accept_3_2 118 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 131 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 116 131 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 131 260 (accept_3_2 115 131 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 131 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 114 131
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 131 260
  (Polychromatic418967fa.accept_11_3_10_7_1_129 113 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 131 260 (accept_3_2 112 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 131 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 110 131 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 131 260 (accept_3_2 109 131 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 131 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 108 131
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 131 260
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 107 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 131 260 (accept_3_2 106 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 131 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 104 131
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 131 260 (accept_3_2 103 131
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 131 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 102 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 131 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 101 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 131 260 (accept_3_2 100 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 131 260 (Polychromatic418967fa.accept_12_2_11_8_1_504
  98 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 131 260 (accept_3_2 97
  131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 131 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 96 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 131 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 95 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 131 260 (accept_3_2 94 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 131 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 92
  131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 131 260 (accept_3_2 91
  131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 131 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 90 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 131 260 (Polychromatic418967fa.accept_18_17_5_8_1_1898 89 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 131 260 (accept_3_2 88 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 131 260 (Polychromatic418967fa.accept_12_2_11_8_1_504
  86 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 131 260 (accept_3_2 85
  131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 131 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 84 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 131 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 131 260 (accept_3_2 82 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 131 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 80
  131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 131 260 (accept_3_2 79
  131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 131 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 78 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 131 260 (Polychromatic418967fa.accept_15_2_11_5_1_1266 77 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 131 260 (accept_3_2 76 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 131 260 (Polychromatic418967fa.accept_7_4_5_1_1_418
  74 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 131 260 (accept_3_2 73
  131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 131 260
  (Polychromatic418967fa.accept_16_8_3_4_1_3233 72 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 131 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 71 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 131 260 (accept_3_2 70 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 131 260 (Polychromatic418967fa.accept_15_8_11_5_1_169
  68 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 131 260 (accept_3_2 67
  131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 131 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 66 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 131 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 260 (accept_3_2 64 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 131 260 (Polychromatic418967fa.accept_7_6_5_1_1_416
  62 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 131 260 (accept_3_2 61
  131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 131 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 131 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 260 (accept_3_2 58 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 56
  131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 131 260 (accept_3_2 55
  131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 131 260
  (Polychromatic418967fa.accept_15_9_11_5_1_1283 54 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 131 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 260 (accept_3_2 52 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 260 (Polychromatic418967fa.accept_12_2_11_8_1_504
  50 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 260 (accept_3_2 49
  131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 131 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 260 (accept_3_2 46 131 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 260
  (Polychromatic418967fa.accept_16_12_3_4_1_4317 44 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 260 (accept_3_2 43 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 260 (accept_3_2 40 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 131 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 260 (accept_3_2 37 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 260 (Polychromatic418967fa.accept_11_3_10_7_1_129 36 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 260 (Polychromatic418967fa.accept_18_17_5_8_1_1898 35 131 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 260 (accept_3_2 34 131 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 131 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 260 (accept_3_2 31 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 260 (accept_3_2 28 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 131 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 260 (accept_3_2 25 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 260 (accept_3_2 22 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 131 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 260 (accept_3_2 19 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 260 (accept_3_2 16 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 260
  (Polychromatic418967fa.accept_11_3_10_7_1_129 14 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 131 260 (accept_3_2 13 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 131 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 131 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 260 (accept_3_2 10 131 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 131 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 260
  (Polychromatic418967fa.accept_15_8_11_5_1_169 8 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 260 (accept_3_2 7 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 260 (Polychromatic418967fa.accept_27_5_23_17_1_15863 5 131 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 260 (accept_3_2 4 131 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 260 (accept_3_2 1 131 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 130 260 (allA_of_3_0 130 130 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 129 260
  (allA_succ_of_accept 128 129 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 128 129 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 129 260 (accept_3_2 127 129 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 129 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 126 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 125 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 129 260 (accept_3_2 124 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 129 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 123 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 129 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 122 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 129 260 (accept_3_2 121 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 129 260 (Polychromatic418967fa.accept_16_8_1_4_1_6622 120 129
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 129 260 (accept_3_2 118 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 129 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 117 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 129 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 116 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 129 260 (accept_3_2 115 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 129 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 114 129
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 129 260 (accept_3_2 112 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 129 260 (Polychromatic418967fa.accept_19_16_15_13_1_1335 111 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 110 129 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 110 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 129 260 (accept_3_2 109 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 129 260 (Polychromatic418967fa.accept_15_3_9_5_1_2082 108 129
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 129 260 (accept_3_2 106 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 129 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 105 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 129 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 104 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 129 260 (accept_3_2 103 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 129 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 102 129
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 129 260 (accept_3_2 100 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 129 260 (Polychromatic418967fa.accept_16_3_1_4_1_5426 99 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 129 260 (Polychromatic418967fa.accept_17_13_10_5_1_2566 98 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 129 260 (accept_3_2 97 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 129 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 96 129 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 129 260 (accept_3_2 94 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 129 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 93 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 129 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 92 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 129 260 (accept_3_2 91 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 129 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 129 260 (accept_3_2 88 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 129 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 129 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 86 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 260 (accept_3_2 85 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 129 260 (Polychromatic418967fa.accept_18_12_3_8_1_6817 84 129 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 129 260 (accept_3_2 82 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 129 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 129 260 (Polychromatic418967fa.accept_17_12_10_5_1_4756 80 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 260 (accept_3_2 79 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 129 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 129 260 (accept_3_2 76 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 129 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 129 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 74 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 260 (accept_3_2 73 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 129 260 (accept_3_2 70 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 129 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 69 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 129 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 260 (accept_3_2 67 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 129 260 (accept_3_2 64 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 129 260 (Polychromatic418967fa.accept_15_3_9_5_1_2082 63 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 129 260 (Polychromatic418967fa.accept_16_14_1_4_1_5432 62 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 260 (accept_3_2 61 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 129 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 129 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 129 260 (accept_3_2 58 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 129 260 (Polychromatic418967fa.accept_15_12_9_5_1_2973 57 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 129 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 260 (accept_3_2 55 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 129 260 (accept_3_2 52 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 129 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 129 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 260 (accept_3_2 49 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 260 (Polychromatic418967fa.accept_11_4_8_7_1_819 48 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 129 260 (accept_3_2 46 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 129 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 129 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 260 (accept_3_2 43 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 260 (accept_3_2 40 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 129 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 129 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 260 (accept_3_2 37 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 260 (Polychromatic418967fa.accept_19_17_15_13_1_7794 36 129 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 260 (accept_3_2 34 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 129 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 129 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 260 (accept_3_2 31 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 260 (accept_3_2 28 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 129 260 (Polychromatic418967fa.accept_15_12_9_5_1_2973 27 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 129 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 260 (accept_3_2 25 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 260 (accept_3_2 22 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 129 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 129 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 260 (accept_3_2 19 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 260 (accept_3_2 16 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 129 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 129 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 260 (accept_3_2 13 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 260 (accept_3_2 10 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 260 (Polychromatic418967fa.accept_16_8_1_4_1_6622 8 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 260 (accept_3_2 7 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 129 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 260 (accept_3_2 4 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 260 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 129 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 260 (accept_3_2 1 129 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 128 260 (allA_succ_of_accept 127 128 260 (accept_3_2 127 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 128 260 2 63 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 128 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 125 128 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 128 260 4 31 32 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 128 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 123 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 128 260 2 61 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 128 260 (accept_3_2 121 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 128 260 4 30 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 128 260 (Polychromatic418967fa.accept_15_14_8_5_1_2104 119 128 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 128 260 2 59 64 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 128 260
  (Polychromatic418967fa.accept_15_12_8_5_1_5048 117 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 128 260 4 29 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 128 260 (accept_3_2 115 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 128 260 2 57 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 128 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 113 128 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 128 260 4 28 32 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 128 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 111 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 128 260 2 55 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 128 260 (accept_3_2 109 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 128 260 4 27 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 128 260 (Polychromatic418967fa.accept_18_17_2_8_1_6800 107 128 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 128 260 2 53 64 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 128 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 105 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 128 260 4 26 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 128 260 (accept_3_2 103 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 128 260 2 51 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 128 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 101 128 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 128 260 4 25 32 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 128 260
  (Polychromatic418967fa.accept_14_1_2_8_1_655 99 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 128 260 2 49 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 128 260 (accept_3_2 97 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 128 260 4 24 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 128 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 128 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 128 260 2 47 64 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 128 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 93 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 128 260 4 23 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 128 260 (accept_3_2 91 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 128 260 2 45 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 128 260 (Polychromatic418967fa.accept_15_14_8_5_1_2104 89 128 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 128 260 4 22 32 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 128 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 87 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 128 260 2 43 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 128 260 (accept_3_2 85 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 128 260 4 21 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 128 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 128 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 128 260 2 41 64 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 128 260
  (Polychromatic418967fa.accept_17_13_9_5_1_6022 81 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 128 260 4 20 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 128 260 (accept_3_2 79 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 128 260 2 39 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 128 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 128 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 128 260 4 19 32 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 128 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 75 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 128 260 2 37 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 128 260 (accept_3_2 73 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 128 260 4 18 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 128 260 (Polychromatic418967fa.accept_14_1_2_8_1_655 71 128 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 128 260 2 35 64 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 128 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 128 260 4 17 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 128 260 (accept_3_2 67 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 128 260 2 33 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 128 260 (Polychromatic418967fa.accept_17_14_9_5_1_4755 65 128 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 128 260 4 16 32 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 128 260
  (Polychromatic418967fa.accept_15_3_8_5_1_2105 63 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 128 260 2 31 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 128 260 (accept_3_2 61 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 128 260 4 15 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 128 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 128 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 128 260 2 29 64 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 128 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 128 260 4 14 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 128 260 (accept_3_2 55 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 128 260 2 27 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 128 260 (Polychromatic418967fa.accept_18_17_2_8_1_6800 53 128 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 260 4 13 32 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 128 260 2 25 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 128 260 (accept_3_2 49 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 128 260 4 12 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 128 260 (Polychromatic418967fa.accept_17_13_9_5_1_6022 47 128 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 128 260 2 23 64 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 128 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 128 260 4 11 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 128 260 (accept_3_2 43 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 128 260 2 21 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 128 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 128 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 260 4 10 32 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 260 2 19 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 260 (accept_3_2 37 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 260 4 9 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 128 260 (Polychromatic418967fa.accept_18_17_2_8_1_6800 35 128 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 260 2 17 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 33
  128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 128 260 4 8 32 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 128 260 (accept_3_2 31
  128 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 128 260 2 15 64 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 128 260
  (Polychromatic418967fa.accept_14_1_2_8_1_655 29 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 128 260 4 7 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 128 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 128 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 128 260 2 13 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 128 260 (accept_3_2 25 128 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 128 260 4 6 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 128 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 128 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 260 2 11 64 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 260 4 5 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 128 260 (accept_3_2 19 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  128 260 2 9 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 128 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 128 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 260 4 4 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 15
  128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 260 2 7 64 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 260 (accept_3_2 13
  128 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 260 4 3 32 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 260
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 128 260 2 5 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 128 260 (Polychromatic418967fa.accept_24_9_8_20_1_9090 9 128 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 260 4 2 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 260 (accept_3_2 7 128 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128 260 2 3 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 128 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 128 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 260 4 1 32 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 128 260 2 1 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 128 260 (accept_3_2 1 128 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 127 260 (allA_of_3_0 127 127 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 126 260
  (allA_succ_of_accept 125 126 260 (Polychromatic418967fa.accept_19_11_12_13_1_4844 125 126 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 126 260 2 62 63 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 126 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 123 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 126 260 2 61 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 126 260 (accept_3_2 121 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 126 260 2 60 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 126 260 (Polychromatic418967fa.accept_11_9_5_7_1_815 119 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 126 260 2 59 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 126 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 117 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 126 260 2 58 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 126 260 (accept_3_2 115 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 126 260 2 57 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 126 260 (Polychromatic418967fa.accept_16_1_14_4_1_3220 113 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 126 260 2 56 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 126 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 111 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 126 260 2 55 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 126 260 (accept_3_2 109 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 126 260 2 54 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 126 260 (Polychromatic418967fa.accept_25_7_1_10_1_14111 107 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 126 260 2 53 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 126 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 105 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 126 260 2 52 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 126 260 (accept_3_2 103 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 126 260 2 51 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 126 260 (Polychromatic418967fa.accept_15_11_6_5_1_1295 101 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 126 260 2 50 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 126 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 99 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 126 260 2 49 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 126 260 (accept_3_2 97 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 126 260 2 48 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 126 260 (Polychromatic418967fa.accept_16_15_14_4_1_6649 95 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 126 260 2 47 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 126 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 93 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 126 260 2 46 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 126 260 (accept_3_2 91 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 126 260 2 45 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 126 260 (Polychromatic418967fa.accept_15_14_6_5_1_7215 89 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 126 260 2 44 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 126 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 87 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 126 260 2 43 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 126 260 (accept_3_2 85 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 126 260 2 42 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 126 260 (Polychromatic418967fa.accept_17_15_7_5_1_9836 83 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 126 260 2 41 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 126 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 126 260 2 40 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 126 260 (accept_3_2 79 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 260 2 39 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 260 (Polychromatic418967fa.accept_17_9_7_5_1_1566 77 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 126 260 2 38 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 126 260
  (Polychromatic418967fa.accept_11_9_5_7_1_815 75 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 126 260 2 37 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 126 260 (accept_3_2 73 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 260 2 36 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 126 260 (Polychromatic418967fa.accept_15_11_6_5_1_1295 71 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 126 260 2 35 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 126 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 126 260 2 34 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 126 260 (accept_3_2 67 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 260 2 33 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 260 (Polychromatic418967fa.accept_16_1_14_4_1_3220 65 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 126 260 2 32 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 126 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 126 260 2 31 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 126 260 (accept_3_2 61 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 260 2 30 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 260 (Polychromatic418967fa.accept_15_14_6_5_1_7215 59 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 260 2 29 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 126 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 126 260 2 28 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 126 260 (accept_3_2 55 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 260 2 27 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 260 (Polychromatic418967fa.accept_11_9_5_7_1_815 53 126 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 260 2 26 63 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 126 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 126 260 2 25 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 126 260 (accept_3_2 49 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 260 2 24 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 126 260 (Polychromatic418967fa.accept_16_15_14_4_1_6649 47 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 260 2 23 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 126 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 126 260 2 22 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 126 260 (accept_3_2 43 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 260 2 21 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 260 (Polychromatic418967fa.accept_15_11_6_5_1_1295 41 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 260 2 20 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 126 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 126 260 2 19 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 126 260 (accept_3_2 37 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 260 2 18 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 260 (Polychromatic418967fa.accept_19_16_12_13_1_4843 35 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 260 2 17 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 126 260 2 16 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 126 260 (accept_3_2 31 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 260 2 15 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 260 (Polychromatic418967fa.accept_15_14_6_5_1_7215 29 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 260 2 14 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 260 2 13 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 260 (accept_3_2 25 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 260 2 12 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 260 (Polychromatic418967fa.accept_16_7_14_4_1_1362 23 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 260 2 11 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 126 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 126 260 2 10 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 126 260 (accept_3_2 19 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 260 2 9 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 126 260 (Polychromatic418967fa.accept_16_1_14_4_1_3220 17 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 260 2 8 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 126 260 2 7 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 126 260 (accept_3_2 13 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 126 260 2 6 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 126 260 (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 260 2 5 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 260
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 126 260 2 4 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 126 260 (accept_3_2 7 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126
  260 2 3 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  126 260 (Polychromatic418967fa.accept_19_5_12_13_1_9115 5 126 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 126 260 2 2 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 126 260 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 126 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 260 2 1 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 260 (accept_3_2 1 126 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 125 260 (allA_succ_of_accept 124 125 260 (accept_3_2 124 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 125 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 123 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 125 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 122 125
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 125 260 (accept_3_2 121 125
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 125 260 5 24 25 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 125 260
  (Polychromatic418967fa.accept_14_7_13_8_1_2067 119 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 125 260 (accept_3_2 118 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 125 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 125 260 (Polychromatic418967fa.accept_19_2_11_13_1_9180 116
  125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 115 125 260 5 23 25 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 114 125 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 114 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 125 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 113 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 125 260 (accept_3_2 112 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 125 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 125 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 125 260 5 22 25 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 125 260 (accept_3_2 109 125 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 125 260
  (Polychromatic418967fa.accept_16_12_13_4_1_3198 108 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 125 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 107 125 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 125 260 (accept_3_2 106 125 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 125 260 5 21 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 125 260
  (Polychromatic418967fa.accept_16_8_13_4_1_3258 104 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 125 260 (accept_3_2 103 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 125 260 (Polychromatic418967fa.accept_11_3_4_7_1_114 102 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 125 260 (Polychromatic418967fa.accept_19_6_11_13_1_4842 101
  125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 125 260 5 20 25 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 125 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 99 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 125 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 98 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 125 260 (accept_3_2 97 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 125 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 96 125 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 125 260 5 19 25 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 125 260 (accept_3_2 94 125 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 125 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 125 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 125 260
  (Polychromatic418967fa.accept_16_12_13_4_1_3198 92 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 125 260 (accept_3_2 91 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 125 260 5 18 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 125 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 89 125 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 125 260 (accept_3_2 88 125 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 125 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 125 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 125 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 86 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 125 260 5 17 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 84 125 260 (Polychromatic418967fa.accept_23_15_10_7_1_4307 84 125 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 125 260
  (Polychromatic418967fa.accept_19_7_11_13_1_11853 83 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 125 260 (accept_3_2 82 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 125 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 125 260 5 16 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 125 260 (accept_3_2 79 125 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 125 260 (Polychromatic418967fa.accept_19_2_11_13_1_9180 78 125 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 125 260
  (Polychromatic418967fa.accept_14_7_13_8_1_2067 77 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 125 260 (accept_3_2 76 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75
  125 260 5 15 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 125 260 (Polychromatic418967fa.accept_11_8_4_7_1_1303 74 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 125 260 (accept_3_2 73 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 125 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 125 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 125 260
  (Polychromatic418967fa.accept_16_7_13_4_1_1348 71 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 125 260 5 14 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 125 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 125 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 125 260 (Polychromatic418967fa.accept_7_5_6_1_1_407
  68 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 125 260 (accept_3_2 67
  125 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 125 260
  (Polychromatic418967fa.accept_23_20_10_7_1_15862 66 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 65 125 260 5 13 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 125 260 (accept_3_2 64 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 125 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 125 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 125
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 260 (accept_3_2 61 125
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 125 260 5 12 25 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 125 260
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 59 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 125 260 (accept_3_2 58 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 125 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 125 260 (Polychromatic418967fa.accept_16_8_13_4_1_3258 56 125 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 125 260 5 11 25 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 125 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 125 260 (Polychromatic418967fa.accept_21_11_20_8_1_8403 53 125 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 260 (accept_3_2 52 125 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 125 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 125 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 125 260 5 10 25 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 125 260 (accept_3_2 49 125 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 125 260
  (Polychromatic418967fa.accept_28_20_13_8_1_15861 48 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 125 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 125 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 260 (accept_3_2 46 125 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 45 125 260 5 9 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 125 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 125 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 260 (accept_3_2 43 125 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 125 260
  (Polychromatic418967fa.accept_28_14_13_8_1_15860 42 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 125 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 125 260 5 8 25 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 125 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 125 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 260 (accept_3_2 37 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 125 260 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 125 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 125 260 5 7 25 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 125 260 (accept_3_2 34 125 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 260
  (Polychromatic418967fa.accept_21_11_20_8_1_8403 32 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 125 260 (accept_3_2 31 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 125 260 5 6 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 125 260 (Polychromatic418967fa.accept_30_29_5_20_1_11681 29 125 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 260 (accept_3_2 28 125 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 125 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 125 260 5 5 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 125 260 (Polychromatic418967fa.accept_16_8_13_4_1_3258 24 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 125 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 260 (accept_3_2 22 125 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 125 260 5 4 25 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 125 260 (accept_3_2 19
  125 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 260
  (Polychromatic418967fa.accept_17_1_6_5_1_3502 18 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 125 260 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 260 (accept_3_2 16 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 125 260 5 3 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 125 260 (Polychromatic418967fa.accept_11_3_4_7_1_114 14 125 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 260 (accept_3_2 13 125 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 125 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 260
  (Polychromatic418967fa.accept_17_11_6_5_1_3662 11 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 125 260 5 2 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 125 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 260 (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 125 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 260 (accept_3_2 7 125 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 260 (Polychromatic418967fa.accept_16_6_13_4_1_643
  6 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 125 260 5 1 25 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 125 260 (accept_3_2 4
  125 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 125 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 125 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 260 (accept_3_2 1 125 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 125
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_260_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


