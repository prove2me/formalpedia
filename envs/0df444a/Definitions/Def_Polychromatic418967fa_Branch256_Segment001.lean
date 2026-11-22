-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch256_Segment001
-- name    : Polychromatic418967fa_Branch256_Segment001
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:47:00.007477+00:00
-- url     : https://prove2.me/theorems/2b7c7e3e-8376-4dc2-80b6-7f7f342034da
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch256_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_256_segment_001 : allB 205 256 :=
  allB_succ' 53 204 256 (Eq.refl Bool.true) (allA_succ_of_gcd 52 204 256 4 13 51 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 204 256
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 51 204 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 204 256 2 25 102 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 204 256 (Polychromatic418967fa.accept_19_11_14_9_1_4599 49 204 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 204 256 4 12 51 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 204 256 (accept_3_3 47 204 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 204 256 2 23 102 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 204 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 204 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 204 256 4 11 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 204 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 204 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 204 256 2 21 102 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 204 256 (accept_3_3 41 204 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 204 256 4 10 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 204 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 39
  204 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 204 256 2 19 102 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 204 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 37 204 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 204 256 4 9 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 204 256 (accept_3_3 35 204 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  204 256 2 17 102 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 204 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 204 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 204 256 4 8 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 204 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 31
  204 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 204 256 2 15 102 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 204 256
  (accept_3_3 29 204 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 204 256 4 7 51 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 204 256
  (Polychromatic418967fa.accept_19_8_14_9_1_4590 27 204 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 204 256 2 13 102 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 204 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 204 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 204 256 4 6 51 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 204 256 (accept_3_3 23 204 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 204 256 2 11 102 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 204 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21
  204 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 204 256 4 5 51 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 204 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 204 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 204 256 2 9 102 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 204 256 (accept_3_3 17 204 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 204 256 4 4 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 204 256 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 204 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 204 256 2 7 102 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 204 256
  (Polychromatic418967fa.accept_22_13_6_14_1_14025 13 204 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 204 256 4 3 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 204 256 (accept_3_3 11 204 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 204 256 2 5 102 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 204 256 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 204 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 204 256 4 2 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 7
  204 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 256 2 3 102 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 256 (accept_3_3 5
  204 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 256 4 1 51 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 204 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 204 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 204 256 2 1 102 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 204 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 204 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204 256)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 54 203 256 (Eq.refl Bool.true) (allA_of_3_1 54 203 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 55 202 256 (Eq.refl Bool.true) (allA_succ_of_gcd 54 202 256 2 27 101 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 202 256 (accept_3_3 53 202 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 202 256 2 26 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 202 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 51
  202 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 202 256 2 25 101 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 202 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 202 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 202 256 2 24 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 202 256 (accept_3_3 47 202 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 202 256 2 23 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 202 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 202 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 202 256 2 22 101 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 202 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 202 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 202 256 2 21 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 202 256 (accept_3_3 41 202 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 202 256 2 20 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 202 256 (Polychromatic418967fa.accept_15_9_7_1_1_1075 39 202 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 202 256 2 19 101 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 202 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 202 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 202 256 2 18 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 202 256 (accept_3_3 35 202 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 202 256 2 17 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 202 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 202 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 202 256 2 16 101 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 202 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 202 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 202 256 2 15 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 202 256 (accept_3_3 29 202 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 202 256 2 14 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 202 256 (Polychromatic418967fa.accept_21_6_13_4_1_6521 27 202 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 202 256 2 13 101 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 202 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 202 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 202 256 2 12 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 202 256 (accept_3_3 23 202 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 202 256 2 11 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 202 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 202 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 202 256 2 10 101 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 202 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 202 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 202 256 2 9 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 202 256 (accept_3_3 17 202 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 202 256 2 8 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 202 256 (Polychromatic418967fa.accept_13_2_7_9_1_2616 15 202 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 202 256 2 7 101 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 202 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 202 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 202 256 2 6 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 202 256 (accept_3_3 11 202 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 202 256 2 5 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 202 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 202 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 202 256 2 4 101 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 202 256
  (Polychromatic418967fa.accept_11_7_4_3_1_302 7 202 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 202 256 2 3 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 202 256 (accept_3_3 5 202 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 202 256 2 2 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 202 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 202 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 256 2 1 101 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 256
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 202 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 256))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 201 256 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 201 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 201 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 201 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 201 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 201 256 (accept_3_3 53 201 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 201 256 (Polychromatic418967fa.accept_9_7_3_4_1_218
  52 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 201 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 201 256 (accept_3_3 50 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 201 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 201 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 201 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 201 256 (accept_3_3 47 201 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 201 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 201 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 201 256
  (Polychromatic418967fa.accept_10_5_1_6_1_672 45 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 201 256 (accept_3_3 44 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 201 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 201 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 201 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 201 256 (accept_3_3 41 201 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 201 256 (Polychromatic418967fa.accept_13_1_6_9_1_1197 40 201 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 201 256
  (Polychromatic418967fa.accept_15_9_6_1_1_493 39 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 201 256 (accept_3_3 38 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 201 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 201 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 201 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 201 256 (accept_3_3 35 201 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 201 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 201 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 201 256 (accept_3_3 32 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 201 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 201 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 201 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 201 256 (accept_3_3 29 201 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 201 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 201 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 201 256 (accept_3_3 26 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 201 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 201 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 201 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 201 256 (accept_3_3 23 201 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 201 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 256
  (Polychromatic418967fa.accept_17_4_14_1_1_1363 21 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 201 256 (accept_3_3 20 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 201 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 201 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 201 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 256 (accept_3_3 17 201 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 201 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 201 256 (accept_3_3 14 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 201 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 201 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 201 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 256 (accept_3_3 11 201 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 201 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 201 256 (accept_3_3 8 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  201 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 201 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 201 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 256 (accept_3_3 5 201 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 256 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 201 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 256
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 3 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 201 256 (accept_3_3 2 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  201 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 201 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 201 256)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 200 256 (Eq.refl
  Bool.true) (allA_of_3_1 57 200 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 199 256 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 199 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 199 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 199 256 (accept_3_3 56 199 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 199 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 199 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 199 256
  (Polychromatic418967fa.accept_22_10_1_14_1_9335 54 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 199 256 (accept_3_3 53 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 199 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 199 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 199 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 199 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 199 256 (accept_3_3 50 199 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 199 256 (Polychromatic418967fa.accept_14_7_3_4_1_1816
  49 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 199 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 199 256 (accept_3_3 47 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 199 256 (Polychromatic418967fa.accept_11_2_1_3_1_683 46 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 199 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 199 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 199 256 (accept_3_3 44 199 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 199 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 199 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 199 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 199 256 (accept_3_3 41 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 199 256 (Polychromatic418967fa.accept_17_6_12_1_1_7043 40 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 199 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 199 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 199 256 (accept_3_3 38 199 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 199 256 (Polychromatic418967fa.accept_20_17_19_16_1_6996 37 199 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 199 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 199 256 (accept_3_3 35 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 199 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 199 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 199 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 199 256 (accept_3_3 32 199 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 199 256 (Polychromatic418967fa.accept_13_5_4_9_1_601 31 199 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 199 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 199 256 (accept_3_3 29 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 199 256 (Polychromatic418967fa.accept_27_1_10_13_1_15647 28 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 199 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 199 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 256 (accept_3_3 26 199 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 199 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 199 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 199 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 199 256 (accept_3_3 23 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 199 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 199 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 199 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 199 256 (accept_3_3 20 199 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 199 256 (Polychromatic418967fa.accept_13_6_4_9_1_4326 19 199 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 256
  (Polychromatic418967fa.accept_13_5_4_9_1_601 18 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 199 256 (accept_3_3 17 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 199 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 199 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 199 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 256 (accept_3_3 14 199 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 199 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 199 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 199 256 (accept_3_3 11 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 199 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 199 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 256 (accept_3_3 8 199 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 199 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 256 (accept_3_3 5 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 256 (Polychromatic418967fa.accept_23_4_15_3_1_15616 4 199 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 199 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 256 (accept_3_3 2 199 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 199 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 198 256 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 198 256 2 29 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 198 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 198 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 198 256 2 28 99 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 198 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 198 256 2 27 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 198 256 (accept_3_3 53 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 198 256 2 26 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 198 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 198 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 198 256 2 25 99 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 198 256
  (Polychromatic418967fa.accept_15_4_3_1_1_487 49 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 198 256 2 24 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 198 256 (accept_3_3 47 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 198 256 2 23 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 198 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 198 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 198 256 2 22 99 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 198 256
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 198 256 2 21 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 198 256 (accept_3_3 41 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 198 256 2 20 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 198 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 198 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 198 256 2 19 99 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 198 256
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 37 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 198 256 2 18 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 198 256 (accept_3_3 35 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 198 256 2 17 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 198 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 198 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 198 256 2 16 99 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 198 256
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 31 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 198 256 2 15 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 198 256 (accept_3_3 29 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 198 256 2 14 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 198 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 198 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 198 256 2 13 99 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 198 256
  (Polychromatic418967fa.accept_13_12_3_9_1_4341 25 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 198 256 2 12 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 198 256 (accept_3_3 23 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 198 256 2 11 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 198 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 198 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 198 256 2 10 99 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 198 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 256 2 9 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 198 256 (accept_3_3 17 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 198 256 2 8 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 198 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 198 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 198 256 2 7 99 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 198 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 256 2 6 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 198 256 (accept_3_3 11 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 198 256 2 5 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 198 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 198 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 198 256 2 4 99 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 256
  (Polychromatic418967fa.accept_13_7_3_9_1_1142 7 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 198 256 2 3 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 198 256 (accept_3_3 5 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 198
  256 2 2 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  198 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 198 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 198 256 2 1 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 198 256 (Polychromatic418967fa.accept_19_1_8_9_1_3304 1 198 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 197 256 (Eq.refl Bool.true) (allA_of_3_1
  60 197 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 196 256 (Eq.refl Bool.true) (allA_succ_of_gcd 60
  196 256 4 15 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 196 256 (accept_3_3 59 196 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58
  196 256 2 29 98 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 196 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 196 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 196 256 4 14 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 196 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 55
  196 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 196 256 2 27 98 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 196 256 (accept_3_3 53
  196 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 196 256 4 13 49 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 196 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 51 196 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 196 256 2 25 98 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 196 256 (Polychromatic418967fa.accept_13_10_1_9_1_3380 49 196 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 196 256 4 12 49 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 196 256 (accept_3_3 47 196 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 196 256 2 23 98 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 196 256
  (Polychromatic418967fa.accept_13_6_1_9_1_619 45 196 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 196 256 4 11 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 196 256 (Polychromatic418967fa.accept_18_7_16_4_1_1674 43 196 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 196 256 2 21 98 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 196 256 (accept_3_3 41 196 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 196 256 4 10 49 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 196 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 196 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 196 256 2 19 98 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 196 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 196 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 196 256 4 9 49 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 196 256 (accept_3_3 35 196 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 196 256 2 17 98 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 196 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 33
  196 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 196 256 4 8 49 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 196 256
  (Polychromatic418967fa.accept_13_5_1_9_1_618 31 196 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 196 256 2 15 98 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 196 256 (accept_3_3 29 196 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 196 256 4 7 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 196 256 (Polychromatic418967fa.accept_17_10_9_1_1_7062 27 196 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 196 256 2 13 98 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 196 256 (Polychromatic418967fa.accept_17_8_9_1_1_3340
  25 196 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 196 256 4 6 49 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 196 256
  (accept_3_3 23 196 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 196 256 2 11 98 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 196 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 196 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 196 256 4 5 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 196 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 196 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 196 256 2 9 98 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 196 256 (accept_3_3 17 196 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 196 256 4 4 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 196 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 196 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 196 256 2 7 98 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 196 256
  (Polychromatic418967fa.accept_19_13_6_9_1_5989 13 196 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 196 256 4 3 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 196 256 (accept_3_3 11 196 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  196 256 2 5 98 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 196 256 (Polychromatic418967fa.accept_22_9_20_14_1_9412 9 196 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 196 256 4 2 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 196 256 (Polychromatic418967fa.accept_18_7_16_4_1_1674 7 196 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 196 256 2 3 98 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 196 256 (accept_3_3 5
  196 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 196 256 4 1 49 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 196 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 196 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 196 256 2 1 98 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 196 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 196 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 196 256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 195 256 (Eq.refl Bool.true) (allA_succ_of_accept 61 195 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  61 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 195 256
  (Polychromatic418967fa.accept_11_5_8_3_1_66 60 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 195 256 (accept_3_3 59 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 195 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 195 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 195 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 195 256 (accept_3_3 56 195 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 195 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 195 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 195 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 195 256 (accept_3_3 53 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 195 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 195 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 195 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 195 256 (accept_3_3 50 195 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 195 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 195 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 195 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 195 256 (accept_3_3 47 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 195 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 195 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 195 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 195 256 (accept_3_3 44 195 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 195 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 195 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 195 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 195 256 (accept_3_3 41 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 195 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 195 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 195 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 195 256 (accept_3_3 38 195 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 195 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 195 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 195 256
  (Polychromatic418967fa.accept_21_15_6_4_1_4990 36 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 195 256 (accept_3_3 35 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 195 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 195 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 195 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 195 256 (accept_3_3 32 195 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 195 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 195 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 195 256 (accept_3_3 29 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 195 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 195 256 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 195 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 195 256 (accept_3_3 26 195 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 195 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 195 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 195 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 195 256 (accept_3_3 23 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 195 256 (Polychromatic418967fa.accept_23_22_11_3_1_10778 22 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 195 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 195 256 (accept_3_3 20 195 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 195 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 195 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 195 256 (accept_3_3 17 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 195 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 195 256 (Polychromatic418967fa.accept_19_15_5_9_1_3299 15 195 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 195 256 (accept_3_3 14 195 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 195 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 195 256 (accept_3_3 11 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 195 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 195 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 195 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 256 (accept_3_3 8 195 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 195 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 256
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 195 256 (accept_3_3 5 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  195 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 195 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 195 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 195 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 256 (accept_3_3 2 195 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 195 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 194 256 (Eq.refl Bool.true)
  (allA_of_3_1 63 194 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 193 256 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 193 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 193 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 193 256 (accept_3_3 62 193 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 193 256 (Polychromatic418967fa.accept_18_7_13_4_1_1670 61 193 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 193 256
  (Polychromatic418967fa.accept_13_8_11_9_1_593 60 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 193 256 (accept_3_3 59 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 193 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 193 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 193 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 193 256 (accept_3_3 56 193 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 193 256 (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 193 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 193 256
  (Polychromatic418967fa.accept_13_2_11_9_1_591 54 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 193 256 (accept_3_3 53 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 193 256 (Polychromatic418967fa.accept_11_8_6_3_1_661 52 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 193 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 193 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 193 256 (accept_3_3 50 193 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 193 256 (Polychromatic418967fa.accept_10_9_3_6_1_686 49 193 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 193 256
  (Polychromatic418967fa.accept_10_8_3_6_1_685 48 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 193 256 (accept_3_3 47 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 193 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 193 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 193 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 193 256 (accept_3_3 44 193 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 193 256 (Polychromatic418967fa.accept_14_1_11_4_1_3430 43 193 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 193 256
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 42 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 193 256 (accept_3_3 41 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 193 256 (Polychromatic418967fa.accept_13_1_11_9_1_1857 40 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 193 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 193 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 193 256 (accept_3_3 38 193 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 193 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 37 193 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 193 256
  (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 193 256 (accept_3_3 35 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 193 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 193 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 193 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 193 256 (accept_3_3 32 193 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 193 256 (Polychromatic418967fa.accept_11_9_6_3_1_1668 31 193 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 193 256
  (Polychromatic418967fa.accept_11_8_6_3_1_661 30 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 193 256 (accept_3_3 29 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 193 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 193 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 193 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 193 256 (accept_3_3 26 193 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 193 256 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 193 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 193 256
  (Polychromatic418967fa.accept_25_24_18_6_1_15646 24 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 193 256 (accept_3_3 23 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 193 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 193 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 193 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 193 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 193 256 (accept_3_3 20 193 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 256 (Polychromatic418967fa.accept_10_9_3_6_1_686
  19 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 193 256
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 193 256 (accept_3_3 17 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 193 256 (Polychromatic418967fa.accept_23_16_9_3_1_10742 16 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 193 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 193 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 256 (accept_3_3 14 193 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 256 (Polychromatic418967fa.accept_19_13_3_9_1_5980 13 193 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 256
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 12 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 193 256 (accept_3_3 11 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 193 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 193 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 193 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 256 (accept_3_3 8 193 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 7
  193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 256
  (Polychromatic418967fa.accept_19_6_3_9_1_3332 6 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 256 (accept_3_3 5 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 256 (Polychromatic418967fa.accept_25_4_18_6_1_15645 4 193 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 193 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 256 (accept_3_3 2 193 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 256 (Polychromatic418967fa.accept_13_1_11_9_1_1857 1 193 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 192 256 (Eq.refl Bool.true)
  (allA_succ_of_gcd 64 192 256 64 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 192 256 (Polychromatic418967fa.accept_11_8_5_3_1_694 63 192 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 192 256 2 31 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 192 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 61
  192 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 192 256 4 15 48 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 192 256 (accept_3_3 59
  192 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 192 256 2 29 96 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 192 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 192 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 192 256 8 7 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 192 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 192 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 192 256 2 27 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 192 256 (accept_3_3 53 192 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 192 256 4 13 48 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 192 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 192 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 192 256 2 25 96 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 192 256
  (Polychromatic418967fa.accept_14_7_10_4_1_130 49 192 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 192 256 16 3 12 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 192 256 (accept_3_3 47 192 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 192 256 2 23 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 192 256 (Polychromatic418967fa.accept_13_6_10_9_1_4329 45 192 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 192 256 4 11 48 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 192 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 192 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 192 256 2 21 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 192 256 (accept_3_3 41 192 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 192 256 8 5 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 192 256 (Polychromatic418967fa.accept_19_1_2_9_1_3314 39 192 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 192 256 2 19 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 192 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 37
  192 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 192 256 4 9 48 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 192 256 (accept_3_3 35
  192 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 192 256 2 17 96 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 192 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 192 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 192 256 32 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 192 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 192 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 192 256 2 15 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 192 256 (accept_3_3 29 192 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 192 256 4 7 48 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 192 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 192 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 192 256 2 13 96 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 192 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 192 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 192 256 8 3 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 192 256 (accept_3_3 23 192 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  192 256 2 11 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 192 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 192 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 192 256 4 5 48 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 192 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 19
  192 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 192 256 2 9 96 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 192 256 (accept_3_3 17
  192 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 192 256 16 1 12 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 192 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 192 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 192 256 2 7 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 192 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 192 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 256 4 3 48 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 256 (accept_3_3 11 192 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 256 2 5 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 192 256 (Polychromatic418967fa.accept_18_9_12_4_1_1659
  9 192 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 192 256 8 1 24 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 192 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 192 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 192 256 2 3 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 192 256 (accept_3_3 5 192 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 192
  256 4 1 48 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  192 256 (Polychromatic418967fa.accept_22_3_16_14_1_13987 3 192 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 192 256 2 1 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 192 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 192 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 191 256 (Eq.refl Bool.true)
  (allA_of_3_1 66 191 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 190 256 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 190 256 2 33 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 190 256 (accept_3_3 65 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 190 256 2 32 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 190 256 (Polychromatic418967fa.accept_13_11_8_9_1_1161 63 190 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 190 256 2 31 95 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 190 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 190 256 2 30 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 190 256 (accept_3_3 59 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 190 256 2 29 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 190 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 190 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 190 256 2 28 95 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 190 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 190 256 2 27 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 190 256 (accept_3_3 53 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 190 256 2 26 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 190 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 190 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 190 256 2 25 95 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 190 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 190 256 2 24 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 190 256 (accept_3_3 47 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 190 256 2 23 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 190 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 190 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 190 256 2 22 95 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 190 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 43 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 190 256 2 21 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 190 256 (accept_3_3 41 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 190 256 2 20 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 190 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 190 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 190 256 2 19 95 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 190 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 190 256 2 18 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 190 256 (accept_3_3 35 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 190 256 2 17 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 190 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 190 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 190 256 2 16 95 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 190 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 190 256 2 15 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 190 256 (accept_3_3 29 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 190 256 2 14 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 190 256 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 190 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 190 256 2 13 95 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 190 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 190 256 2 12 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 190 256 (accept_3_3 23 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 190 256 2 11 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 190 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 190 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 190 256 2 10 95 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 190 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 190 256 2 9 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 190 256 (accept_3_3 17 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 190 256 2 8 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 190 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 190 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 190 256 2 7 95 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 190 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 190 256 2 6 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 190 256 (accept_3_3 11 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 190 256 2 5 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 190 256 (Polychromatic418967fa.accept_15_9_10_1_1_1062 9 190 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 190 256 2 4 95 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 190 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 190 256 2 3 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 190 256 (accept_3_3 5 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 190
  256 2 2 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  190 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 190 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 190 256 2 1 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 190 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 190 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 189 256 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 189 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 189 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 189 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 66 189 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 189 256 (accept_3_3 65 189 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 189 256
  (Polychromatic418967fa.accept_17_13_2_1_1_4483 64 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 189 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 63 189 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 189 256 (accept_3_3 62 189 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 189 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 189 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 189 256 (Polychromatic418967fa.accept_13_8_7_9_1_611
  60 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 189 256 (accept_3_3 59
  189 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 189 256
  (Polychromatic418967fa.accept_13_6_7_9_1_1848 58 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 189 256 (Polychromatic418967fa.accept_17_6_2_1_1_3350 57 189 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 189 256 (accept_3_3 56 189 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 189 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 189 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 189 256 (Polychromatic418967fa.accept_12_6_9_4_1_96
  54 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 189 256 (accept_3_3 53
  189 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 189 256
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 52 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 189 256 (Polychromatic418967fa.accept_15_6_9_1_1_1823 51 189 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 189 256 (accept_3_3 50 189 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 189 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 189 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 189 256
  (Polychromatic418967fa.accept_18_12_9_4_1_2740 48 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 189 256 (accept_3_3 47 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 189 256 (Polychromatic418967fa.accept_19_8_18_9_1_10160 46 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 189 256 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 189 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 189 256 (accept_3_3 44 189 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 189 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 189 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 189 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 189 256 (accept_3_3 41 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 189 256 (Polychromatic418967fa.accept_15_10_9_1_1_3688 40 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 189 256 (Polychromatic418967fa.accept_14_11_7_4_1_3449 39 189 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 189 256 (accept_3_3 38 189 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 189 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 189 256
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 189 256 (accept_3_3 35 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 189 256 (Polychromatic418967fa.accept_11_1_2_3_1_688 34 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 189 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 33 189 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 189 256 (accept_3_3 32 189 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 189 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 189 256 (accept_3_3 29 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 189 256 (Polychromatic418967fa.accept_13_2_7_9_1_2616 28 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 189 256 (Polychromatic418967fa.accept_19_8_18_9_1_10160 27 189 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 189 256 (accept_3_3 26 189 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 189 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 256
  (Polychromatic418967fa.accept_13_11_7_9_1_612 24 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 189 256 (accept_3_3 23 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 189 256 (Polychromatic418967fa.accept_15_7_9_1_1_473 22 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 189 256 (Polychromatic418967fa.accept_13_8_7_9_1_611 21 189 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 189 256 (accept_3_3 20 189 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 189 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 189 256 (accept_3_3 17 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 189 256 (Polychromatic418967fa.accept_13_3_7_9_1_1153 16 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 189 256 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 189 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 189 256 (accept_3_3 14 189 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 189 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 256
  (Polychromatic418967fa.accept_11_1_2_3_1_688 12 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 189 256 (accept_3_3 11 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 189 256 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 189 256 (Polychromatic418967fa.accept_29_9_15_24_1_15644 9 189 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 256 (accept_3_3 8 189 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 189 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 189 256 (accept_3_3 5 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  189 256 (Polychromatic418967fa.accept_13_4_7_9_1_5260 4 189 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 189 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 189 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 256 (accept_3_3 2 189 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 189 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 188 256 (Eq.refl Bool.true)
  (allA_of_3_1 69 188 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 187 256 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 187 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 187 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 187 256 (accept_3_3 68 187 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 187 256 (Polychromatic418967fa.accept_13_2_5_9_1_610 67 187 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 187 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 187 256 (accept_3_3 65 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 187 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 187 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 187 256 (accept_3_3 62 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 187 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 61 187 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 187 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 187 256 (accept_3_3 59 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 187 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 187 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 187 256 (accept_3_3 56 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 187 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 187 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 187 256
  (Polychromatic418967fa.accept_13_2_5_9_1_610 54 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 187 256 (accept_3_3 53 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 187 256 (Polychromatic418967fa.accept_18_16_7_4_1_3901 52 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 187 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 187 256 (accept_3_3 50 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 187 256 (Polychromatic418967fa.accept_18_13_7_4_1_2738 49 187 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 187 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 187 256 (accept_3_3 47 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 187 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 187 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 187 256 (accept_3_3 44 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 187 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 187 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 187 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 187 256 (accept_3_3 41 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 187 256 (Polychromatic418967fa.accept_13_1_5_9_1_226 40 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 187 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 187 256 (accept_3_3 38 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 187 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 187 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 187 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 187 256 (accept_3_3 35 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 187 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 187 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 187 256 (accept_3_3 32 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 187 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 31 187 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 187 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 187 256 (accept_3_3 29 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 187 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 187 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 187 256 (accept_3_3 26 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 187 256 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 187 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 187 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 187 256 (accept_3_3 23 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 187 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 187 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 187 256 (accept_3_3 20 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 187 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 187 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 187 256
  (Polychromatic418967fa.accept_19_18_16_9_1_4556 18 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 187 256 (accept_3_3 17 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 187 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 187 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 187 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 187 256 (accept_3_3 14 187 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 187 256 (Polychromatic418967fa.accept_7_6_5_4_1_297
  13 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 187 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 187 256 (accept_3_3 11 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 187 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 187 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 256 (accept_3_3 8 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 256 (Polychromatic418967fa.accept_19_7_16_9_1_398 7 187 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 187 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 187 256 (accept_3_3 5 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  187 256 (Polychromatic418967fa.accept_13_4_5_9_1_1829 4 187 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 187 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 256 (accept_3_3 2 187 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 187 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 186 256 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 186 256 2 35 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 186 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 186 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 186 256 2 34 93 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 186 256
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 67 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 186 256 2 33 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 186 256 (accept_3_3 65 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 186 256 2 32 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 186 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 186 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 186 256 2 31 93 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 186 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 61 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 186 256 2 30 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 186 256 (accept_3_3 59 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 186 256 2 29 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 186 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 186 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 186 256 2 28 93 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 186 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 55 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 186 256 2 27 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 186 256 (accept_3_3 53 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 186 256 2 26 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 186 256 (Polychromatic418967fa.accept_11_7_10_3_1_633 51 186 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 186 256 2 25 93 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 186 256
  (Polychromatic418967fa.accept_17_15_16_1_1_7080 49 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 186 256 2 24 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 186 256 (accept_3_3 47 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 186 256 2 23 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 186 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 186 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 186 256 2 22 93 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 186 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 186 256 2 21 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 186 256 (accept_3_3 41 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 186 256 2 20 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 186 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 186 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 186 256 2 19 93 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 186 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 37 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 186 256 2 18 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 186 256 (accept_3_3 35 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 186 256 2 17 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 186 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 186 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 186 256 2 16 93 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 186 256
  (Polychromatic418967fa.accept_13_5_4_9_1_601 31 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 256 2 15 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 256 (accept_3_3 29 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 186 256 2 14 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 186 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 186 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 186 256 2 13 93 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 186 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 256 2 12 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 186 256 (accept_3_3 23 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 186 256 2 11 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 186 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 186 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 186 256 2 10 93 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 186 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 19 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 256 2 9 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 256 (accept_3_3 17 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 186 256 2 8 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 186 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 186 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 186 256 2 7 93 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 186 256
  (Polychromatic418967fa.accept_19_13_15_9_1_3293 13 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 186 256 2 6 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 186 256 (accept_3_3 11 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 186 256 2 5 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 186 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 186 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 186 256 2 4 93 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 186 256 2 3 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 186 256 (accept_3_3 5 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 186
  256 2 2 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  186 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 186 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 186 256 2 1 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 186 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 186 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 185 256 (Eq.refl Bool.true)
  (allA_of_3_1 72 185 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 184 256 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 184 256 8 9 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 184 256 (accept_3_3 71 184 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  184 256 2 35 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 184 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 184 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 184 256 4 17 46 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 184 256
  (Polychromatic418967fa.accept_19_10_13_9_1_4552 67 184 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 184 256 2 33 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 184 256 (accept_3_3 65 184 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 184 256 8 8 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 184 256 (Polychromatic418967fa.accept_13_11_2_9_1_2640 63 184 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 184 256 2 31 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 184 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 61
  184 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 184 256 4 15 46 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 184 256 (accept_3_3 59
  184 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 184 256 2 29 92 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 184 256
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 57 184 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 184 256 8 7 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 184 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 184 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 184 256 2 27 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 184 256 (accept_3_3 53 184 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 184 256 4 13 46 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 184 256 (Polychromatic418967fa.accept_14_9_2_4_1_1814 51 184
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 184 256 2 25 92 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 184 256
  (Polychromatic418967fa.accept_11_5_8_3_1_66 49 184 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 184 256 8 6 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 184 256 (accept_3_3 47 184 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  184 256 2 23 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 184 256 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 184 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 184 256 4 11 46 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 184 256 (Polychromatic418967fa.accept_19_5_13_9_1_5957
  43 184 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 184 256 2 21 92 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 184 256
  (accept_3_3 41 184 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 184 256 8 5 23 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 184 256
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 184 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 184 256 2 19 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 184 256 (Polychromatic418967fa.accept_13_11_2_9_1_2640 37 184 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 184 256 4 9 46 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 184 256 (accept_3_3 35 184 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 184 256 2 17 92 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 184 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 184 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 184 256 8 4 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 184 256 (Polychromatic418967fa.accept_13_5_2_9_1_1195 31 184 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 184 256 2 15 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 184 256 (accept_3_3 29 184 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 184 256 4 7 46 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 184 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 184 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 184 256 2 13 92 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 184 256
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 184 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 184 256 8 3 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 184 256 (accept_3_3 23 184 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  184 256 2 11 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 184 256 (Polychromatic418967fa.accept_17_4_14_1_1_1363 21 184 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 184 256 4 5 46 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 184 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 19
  184 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 184 256 2 9 92 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 184 256 (accept_3_3 17
  184 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 184 256 8 2 23 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 184 256
  (Polychromatic418967fa.accept_10_5_4_6_1_319 15 184 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 184 256 2 7 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 184 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 184 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 184 256 4 3 46 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 184 256 (accept_3_3 11 184 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 184 256 2 5 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 184 256 (Polychromatic418967fa.accept_14_9_2_4_1_1814 9
  184 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 184 256 8 1 23 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 184 256
  (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 184 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 184 256 2 3 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 184 256 (accept_3_3 5 184 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184
  256 4 1 46 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  184 256 (Polychromatic418967fa.accept_13_3_2_9_1_1187 3 184 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 184 256 2 1 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 184 256 (Polychromatic418967fa.accept_13_1_2_9_1_1186 1 184 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 183 256 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 183 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 183 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 183 256
  (Polychromatic418967fa.accept_21_9_15_4_1_2190 72 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 183 256 (accept_3_3 71 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 183 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 183 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 183 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 183 256 (accept_3_3 68 183 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 183 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 183 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 183 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 66 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 183 256 (accept_3_3 65 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 183 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 183 256 (Polychromatic418967fa.accept_13_11_1_9_1_1179 63 183 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 183 256 (accept_3_3 62 183 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 183 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 183 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 183 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 183 256 (accept_3_3 59 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 183 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 183 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 57 183 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 183 256 (accept_3_3 56 183 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 183 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 183 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 183 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 183 256 (accept_3_3 53 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 183 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 183 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 183 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 183 256 (accept_3_3 50 183 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 183 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 183 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 183 256
  (Polychromatic418967fa.accept_10_8_3_6_1_685 48 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 183 256 (accept_3_3 47 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 183 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 183 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 183 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 183 256 (accept_3_3 44 183 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 183 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 183 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 183 256 (accept_3_3 41 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 183 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 183 256 (Polychromatic418967fa.accept_10_9_3_6_1_686 39 183 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 183 256 (accept_3_3 38 183 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 183 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 183 256
  (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 183 256 (accept_3_3 35 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 183 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 183 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 183 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 183 256 (accept_3_3 32 183 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 183 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 183 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 183 256 (accept_3_3 29 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 183 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 183 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 183 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 183 256 (accept_3_3 26 183 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 183 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 183 256 (accept_3_3 23 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 183 256 (Polychromatic418967fa.accept_19_3_12_9_1_3308 22 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 183 256 (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 183 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 183 256 (accept_3_3 20 183 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 183 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 183 256
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 183 256 (accept_3_3 17 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 183 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 183 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 183 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 256 (accept_3_3 14 183 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 183 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 183 256 (accept_3_3 11 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 183 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 183 256 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 183 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 256 (accept_3_3 8 183 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 183 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 183 256 (accept_3_3 5 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  183 256 (Polychromatic418967fa.accept_11_4_7_3_1_289 4 183 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 183 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 183 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 256 (accept_3_3 2 183 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 183 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 182 256 (Eq.refl
  Bool.true) (allA_of_3_1 75 182 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 181 256 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 181 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 181 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 181 256 (accept_3_3 74 181 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 181 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 181 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 72
  181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 181 256 (accept_3_3 71
  181 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 181 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 70 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 181 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 181 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 181 256 (accept_3_3 68 181 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 181 256 (Polychromatic418967fa.accept_10_7_1_6_1_673 67 181 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 181 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 66 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 181 256 (accept_3_3 65 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 181 256 (Polychromatic418967fa.accept_19_7_10_9_1_2162 64 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 181 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 181 256 (accept_3_3 62 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 181 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 181 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 181 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 181 256 (accept_3_3 59 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 181 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 181 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 181 256 (accept_3_3 56 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 181 256 (Polychromatic418967fa.accept_10_5_1_6_1_672 55 181 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 181 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 181 256 (accept_3_3 53 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 181 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 181 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 181 256 (accept_3_3 50 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 181 256 (Polychromatic418967fa.accept_13_10_12_9_1_1837 49 181 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 181 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 181 256 (accept_3_3 47 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 181 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 181 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 181 256 (accept_3_3 44 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 181 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 181 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 181 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 181 256 (accept_3_3 41 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 181 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 181 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 181 256 (accept_3_3 38 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 181 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 181 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 181 256
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 181 256 (accept_3_3 35 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 181 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 181 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 181 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 181 256 (accept_3_3 32 181 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 181 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 31
  181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 181 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 181 256 (accept_3_3 29 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 181 256 (Polychromatic418967fa.accept_21_7_13_4_1_2169 28 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 181 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 181 256 (accept_3_3 26 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 181 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 181 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 181 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 181 256 (accept_3_3 23 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 181 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 181 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 181 256 (accept_3_3 20 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 181 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 181 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 181 256
  (Polychromatic418967fa.accept_19_18_10_9_1_5996 18 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 181 256 (accept_3_3 17 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 181 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 181 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 181 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 181 256 (accept_3_3 14 181 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 181 256
  (Polychromatic418967fa.accept_19_13_10_9_1_5995 13 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 256 (accept_3_3 11 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 181 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 256 (accept_3_3 8 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 256 (accept_3_3 5 181 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 256 (Polychromatic418967fa.accept_19_4_10_9_1_4569 4 181 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 256 (accept_3_3 2 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 256 (Polychromatic418967fa.accept_19_1_10_9_1_10302 1 181 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  77 180 256 (Eq.refl Bool.true) (allA_succ_of_gcd 76 180 256 4 19 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 180 256 (Polychromatic418967fa.accept_17_7_10_1_1_4488
  75 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 180 256 2 37 90 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 180 256
  (Polychromatic418967fa.accept_11_7_4_3_1_302 73 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 180 256 4 18 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 180 256 (accept_3_3 71 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 180 256 2 35 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 180 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 180 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 180 256 4 17 45 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 180 256
  (Polychromatic418967fa.accept_13_2_11_9_1_591 67 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 180 256 2 33 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 180 256 (accept_3_3 65 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 180 256 4 16 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 180 256 (Polychromatic418967fa.accept_26_11_24_22_1_15643 63 180 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 180 256 2 31 90 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 180 256
  (Polychromatic418967fa.accept_21_19_12_4_1_8134 61 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 180 256 4 15 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 180 256 (accept_3_3 59 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 180 256 2 29 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 180 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 180 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 180 256 4 14 45 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 180 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 55 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 180 256 2 27 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 180 256 (accept_3_3 53 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 180 256 4 13 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 180 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 180 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 180 256 2 25 90 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 180 256
  (Polychromatic418967fa.accept_21_7_12_4_1_6493 49 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 180 256 4 12 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 180 256 (accept_3_3 47 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 180 256 2 23 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 180 256 (Polychromatic418967fa.accept_17_11_10_1_1_13244 45 180 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 180 256 4 11 45 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 180 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 180 256 2 21 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 180 256 (accept_3_3 41 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 180 256 4 10 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 180 256 (Polychromatic418967fa.accept_21_18_12_4_1_4967 39 180 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 180 256 2 19 90 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 180 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 180 256 4 9 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 180 256 (accept_3_3 35 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  180 256 2 17 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 180 256 (Polychromatic418967fa.accept_13_7_11_9_1_1858 33 180 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 180 256 4 8 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 180 256
  (Polychromatic418967fa.accept_17_14_10_1_1_4523 31 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 180 256 2 15 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 180 256 (accept_3_3 29 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 180 256 4 7 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 180 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 180 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 180 256 2 13 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 180 256
  (Polychromatic418967fa.accept_22_3_4_14_1_14022 25 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 180 256 4 6 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 180 256 (accept_3_3 23 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 180 256 2 11 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 180 256 (Polychromatic418967fa.accept_13_8_11_9_1_593 21 180 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 180 256 4 5 45 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 256
  (Polychromatic418967fa.accept_21_19_12_4_1_8134 19 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 180 256 2 9 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 180 256 (accept_3_3 17 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 180 256 4 4 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 180 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 180 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 180 256 2 7 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 13
  180 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 256 4 3 45 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 256 (accept_3_3 11
  180 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 256 2 5 90 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 180 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 180 256 4 2 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 180 256 (Polychromatic418967fa.accept_11_7_4_3_1_302 7 180 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 256 2 3 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 180 256 (accept_3_3 5 180 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180 256 4 1 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 180 256 (Polychromatic418967fa.accept_21_3_12_4_1_8116 3 180 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 180 256 2 1 90 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 180 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 180 256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 179 256
  (Eq.refl Bool.true) (allA_of_3_1 78 179 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 178 256 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 178 256 2 39 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 178 256 (accept_3_3 77 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 178 256 2 38 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 178 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 75 178 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 178 256 2 37 89 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 178 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 73 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 178 256 2 36 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 178 256 (accept_3_3 71 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 178 256 2 35 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 178 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 178 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 178 256 2 34 89 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 178 256
  (Polychromatic418967fa.accept_11_1_2_3_1_688 67 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 178 256 2 33 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 178 256 (accept_3_3 65 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 178 256 2 32 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 178 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 178 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 178 256 2 31 89 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 178 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 178 256 2 30 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 178 256 (accept_3_3 59 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 178 256 2 29 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 178 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 178 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 178 256 2 28 89 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 178 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 55 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 178 256 2 27 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 178 256 (accept_3_3 53 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 178 256 2 26 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 178 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 178 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 178 256 2 25 89 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 178 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 178 256 2 24 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 178 256 (accept_3_3 47 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 178 256 2 23 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 178 256 (Polychromatic418967fa.accept_11_1_2_3_1_688 45 178 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 178 256 2 22 89 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 178 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 178 256 2 21 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 178 256 (accept_3_3 41 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 178 256 2 20 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 178 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 178 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 178 256 2 19 89 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 178 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 37 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 178 256 2 18 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 178 256 (accept_3_3 35 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 178 256 2 17 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 178 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 178 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 178 256 2 16 89 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 178 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 178 256 2 15 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 178 256 (accept_3_3 29 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 178 256 2 14 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 178 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 178 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 178 256 2 13 89 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 178 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 178 256 2 12 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 178 256 (accept_3_3 23 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 178 256 2 11 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 178 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 178 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 178 256 2 10 89 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 178 256 2 9 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 178 256 (accept_3_3 17 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 256 2 8 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 178 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 178 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 256 2 7 89 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 256 2 6 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 256 (accept_3_3 11 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 256 2 5 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 256 (Polychromatic418967fa.accept_17_9_8_1_1_7036 9 178 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 256 2 4 89 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 256 2 3 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 256 (accept_3_3 5 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  256 2 2 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 178 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 256 2 1 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 178 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 177 256 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 177 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 177 256 (Polychromatic418967fa.accept_12_6_9_4_1_96
  78 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 177 256 (accept_3_3 77
  177 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 177 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 76 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 177 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 177 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 177 256 (accept_3_3 74 177 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 177 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 177 256 (Polychromatic418967fa.accept_13_7_8_9_1_1158
  72 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 177 256 (accept_3_3 71
  177 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 177 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 70 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 177 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 177 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 177 256 (accept_3_3 68 177 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 177 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 177 256 (Polychromatic418967fa.accept_9_3_6_4_1_210
  66 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 177 256 (accept_3_3 65
  177 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 177 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 64 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 177 256 (Polychromatic418967fa.accept_10_3_7_6_1_659 63 177 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 177 256 (accept_3_3 62 177 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 177 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 177 256
  (Polychromatic418967fa.accept_18_6_15_4_1_3916 60 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 177 256 (accept_3_3 59 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 177 256 (Polychromatic418967fa.accept_14_2_9_4_1_1735 58 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 177 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 177 256 (accept_3_3 56 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 177 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 177 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 177 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 177 256 (accept_3_3 53 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 177 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 177 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 51 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 177 256 (accept_3_3 50 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 177 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 177 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 177 256 (accept_3_3 47 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 177 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 177 256 (Polychromatic418967fa.accept_17_11_7_1_1_7023 45 177 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 177 256 (accept_3_3 44 177 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 177 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 177 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 177 256 (accept_3_3 41 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 177 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 177 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 177 256 (accept_3_3 38 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 177 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 256
  (Polychromatic418967fa.accept_19_17_6_9_1_8856 36 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 177 256 (accept_3_3 35 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 177 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 177 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 177 256 (accept_3_3 32 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 177 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 177 256 (accept_3_3 29 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 177 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 177 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 256 (accept_3_3 26 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 177 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 256
  (Polychromatic418967fa.accept_11_2_1_3_1_683 24 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 177 256 (accept_3_3 23 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 177 256 (Polychromatic418967fa.accept_19_3_6_9_1_7334 22 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 177 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 256 (accept_3_3 20 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 177 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 177 256 (accept_3_3 17 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 177 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 177 256 (Polychromatic418967fa.accept_19_15_6_9_1_3334 15 177 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 256 (accept_3_3 14 177 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 177 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 177 256 (accept_3_3 11 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 177 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 177 256 (Polychromatic418967fa.accept_18_9_15_4_1_5173 9 177 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 256 (accept_3_3 8 177 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 177 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 177 256 (accept_3_3 5 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  177 256 (Polychromatic418967fa.accept_13_4_8_9_1_1156 4 177 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 177 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 256 (accept_3_3 2 177 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 177 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 176 256 (Eq.refl
  Bool.true) (allA_of_3_1 81 176 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 175 256 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 175 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 175 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 175 256 (accept_3_3 80 175 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 175 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 79 175 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 175 256
  (Polychromatic418967fa.accept_19_2_4_9_1_1131 78 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 175 256 (accept_3_3 77 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 175 256 (Polychromatic418967fa.accept_21_13_7_4_1_4991 76 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 175 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 175 256 (accept_3_3 74 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 175 256 (Polychromatic418967fa.accept_11_7_10_3_1_633 73 175 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 175 256
  (Polychromatic418967fa.accept_13_7_6_9_1_1831 72 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 175 256 (accept_3_3 71 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 175 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 175 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 175 256 (accept_3_3 68 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 175 256 (Polychromatic418967fa.accept_13_2_6_9_1_2636 67 175 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 175 256
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 66 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 175 256 (accept_3_3 65 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 175 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 64 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 175 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 175 256 (accept_3_3 62 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 175 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 61 175 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 175 256
  (Polychromatic418967fa.accept_21_18_7_4_1_8131 60 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 175 256 (accept_3_3 59 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 175 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 175 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 175 256 (accept_3_3 56 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 175 256 (Polychromatic418967fa.accept_13_3_6_9_1_1150 55 175 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 175 256
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 175 256 (accept_3_3 53 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 175 256 (Polychromatic418967fa.accept_14_10_7_4_1_3453 52 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 175 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 175 256 (accept_3_3 50 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 175 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 49 175 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 175 256
  (Polychromatic418967fa.accept_19_10_4_9_1_7333 48 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 175 256 (accept_3_3 47 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 175 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 175 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 175 256 (accept_3_3 44 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 175 256 (Polychromatic418967fa.accept_13_4_6_9_1_3401 43 175 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 175 256
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 42 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 175 256 (accept_3_3 41 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 175 256 (Polychromatic418967fa.accept_11_7_10_3_1_633 40 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 175 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 175 256 (accept_3_3 38 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 175 256 (Polychromatic418967fa.accept_15_7_10_1_1_1836 37 175 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 175 256
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 175 256 (accept_3_3 35 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 175 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 175 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 175 256 (accept_3_3 32 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 175 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 175 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 175 256
  (Polychromatic418967fa.accept_13_4_6_9_1_3401 30 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 175 256 (accept_3_3 29 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 175 256 (Polychromatic418967fa.accept_13_2_6_9_1_2636 28 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 175 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 256 (accept_3_3 26 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 175 256 (Polychromatic418967fa.accept_14_11_7_4_1_3449 25 175 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 175 256
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 175 256 (accept_3_3 23 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 175 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 175 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 175 256 (accept_3_3 20 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 175 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 175 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 175 256
  (Polychromatic418967fa.accept_11_7_10_3_1_633 18 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 175 256 (accept_3_3 17 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 175 256 (Polychromatic418967fa.accept_13_3_6_9_1_1150 16 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 175 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 175 256 (accept_3_3 14 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 175 256 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 175 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 175 256
  (Polychromatic418967fa.accept_21_12_7_4_1_12629 12 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 175 256 (accept_3_3 11 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 175 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 175 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 175 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 256 (accept_3_3 8 175 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 256 (Polychromatic418967fa.accept_11_7_10_3_1_633
  7 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 256
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 6 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 175 256 (accept_3_3 5 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  175 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 175 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 175 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 256 (accept_3_3 2 175 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 175 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 174 256 (Eq.refl
  Bool.true) (allA_succ_of_gcd 82 174 256 2 41 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 174 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 81 174 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 174 256 2 40 87 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 174 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 79 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 174 256 2 39 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 174 256 (accept_3_3 77 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 174 256 2 38 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 174 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 174 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 174 256 2 37 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 174 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 73 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 174 256 2 36 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 174 256 (accept_3_3 71 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 174 256 2 35 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 174 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 174 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 174 256 2 34 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 174 256
  (Polychromatic418967fa.accept_13_2_5_9_1_610 67 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 174 256 2 33 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 174 256 (accept_3_3 65 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 174 256 2 32 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 174 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 174 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 174 256 2 31 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 174 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 61 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 174 256 2 30 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 174 256 (accept_3_3 59 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 174 256 2 29 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 174 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 174 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 174 256 2 28 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 174 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 55 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 174 256 2 27 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 174 256 (accept_3_3 53 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 174 256 2 26 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 174 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 174 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 174 256 2 25 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 174 256
  (Polychromatic418967fa.accept_19_11_3_9_1_8882 49 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 256 2 24 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 174 256 (accept_3_3 47 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 174 256 2 23 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 174 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 174 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 174 256 2 22 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 174 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 256 2 21 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 174 256 (accept_3_3 41 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 174 256 2 20 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 174 256 (Polychromatic418967fa.accept_11_6_9_3_1_1103 39 174 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 174 256 2 19 87 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 174 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 256 2 18 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 256 (accept_3_3 35 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 174 256 2 17 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 174 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 174 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 174 256 2 16 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 256 2 15 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 256 (accept_3_3 29 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 174 256 2 14 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 174 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 174 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 174 256 2 13 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 174 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 256 2 12 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 256 (accept_3_3 23 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 174 256 2 11 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 174 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 174 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 174 256 2 10 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 256 2 9 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 256 (accept_3_3 17 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 174 256 2 8 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 174 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 174 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 174 256 2 7 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 256
  (Polychromatic418967fa.accept_19_13_3_9_1_5980 13 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 256 2 6 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 256 (accept_3_3 11 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 174 256 2 5 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 174 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 174 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 174 256 2 4 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 174 256 2 3 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 174 256 (accept_3_3 5 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174
  256 2 2 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  174 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 174 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 174 256 2 1 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 174 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 174 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 173 256 (Eq.refl
  Bool.true) (allA_of_3_1 84 173 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 85 172 256 (Eq.refl Bool.true)
  (allA_succ_of_gcd 84 172 256 4 21 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 172 256 (accept_3_3 83 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 172 256 2 41 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 172 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 172 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 172 256 4 20 43 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 172 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 79 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 172 256 2 39 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 172 256 (accept_3_3 77 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 172 256 4 19 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 172 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 75 172 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 172 256 2 37 86 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 172 256
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 73 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 172 256 4 18 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 172 256 (accept_3_3 71 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 172 256 2 35 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 172 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 172 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 172 256 4 17 43 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 172 256
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 67 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 172 256 2 33 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 172 256 (accept_3_3 65 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 172 256 4 16 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 172 256 (Polychromatic418967fa.accept_24_15_4_16_1_8786 63 172 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 172 256 2 31 86 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 172 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 61 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 172 256 4 15 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 172 256 (accept_3_3 59 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 172 256 2 29 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 172 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 172 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 172 256 4 14 43 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 172 256
  (Polychromatic418967fa.accept_15_10_7_1_1_3686 55 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 172 256 2 27 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 172 256 (accept_3_3 53 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 172 256 4 13 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 172 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 172 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 172 256 2 25 86 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 172 256
  (Polychromatic418967fa.accept_18_13_10_4_1_5150 49 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 172 256 4 12 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 172 256 (accept_3_3 47 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 172 256 2 23 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 172 256 (Polychromatic418967fa.accept_13_6_3_9_1_1827 45 172 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 172 256 4 11 43 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 172 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 43 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 172 256 2 21 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 172 256 (accept_3_3 41 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 172 256 4 10 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 172 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 172 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 172 256 2 19 86 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 172 256
  (Polychromatic418967fa.accept_11_4_7_3_1_289 37 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 172 256 4 9 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 172 256 (accept_3_3 35 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  172 256 2 17 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 172 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 172 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 172 256 4 8 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 172 256 (Polychromatic418967fa.accept_10_1_2_6_1_638
  31 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 172 256 2 15 86 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 172 256
  (accept_3_3 29 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 172 256 4 7 43 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 172 256
  (Polychromatic418967fa.accept_19_8_1_9_1_7329 27 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 172 256 2 13 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 172 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 172 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 172 256 4 6 43 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 172 256 (accept_3_3 23 172 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 172 256 2 11 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 172 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 21
  172 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 172 256 4 5 43 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 172 256
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 19 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 172 256 2 9 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 172 256 (accept_3_3 17 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 172 256 4 4 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 172 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 172 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 172 256 2 7 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 256 (Polychromatic418967fa.accept_17_13_2_1_1_4483
  13 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 172 256 4 3 43 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 172 256
  (accept_3_3 11 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 172 256 2 5 86 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 172 256
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 172 256 4 2 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 172 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 172 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 172 256 2 3 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 172 256 (accept_3_3 5 172 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172 256 4 1 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 172 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 172 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 172 256 2 1 86 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 172 256
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 172 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 172 256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86
  171 256 (Eq.refl Bool.true) (allA_succ_of_accept 85 171 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 171 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 171 256
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 84 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 171 256 (accept_3_3 83 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 171 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 82 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 171 256 (Polychromatic418967fa.accept_13_3_2_9_1_1187 81 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 171 256 (accept_3_3 80 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 171 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 171 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 171 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 78 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 171 256 (accept_3_3 77 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 171 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 171 256 (Polychromatic418967fa.accept_10_5_1_6_1_672 75 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 171 256 (accept_3_3 74 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 171 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 171 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 171 256
  (Polychromatic418967fa.accept_10_2_1_6_1_634 72 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 171 256 (accept_3_3 71 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 171 256 (Polychromatic418967fa.accept_13_5_2_9_1_1195 70 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 171 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 171 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 171 256 (accept_3_3 68 171 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 171 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 171 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 171 256 (accept_3_3 65 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 171 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 171 256 (Polychromatic418967fa.accept_11_8_6_3_1_661 63 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 171 256 (accept_3_3 62 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 171 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 171 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 171 256
  (Polychromatic418967fa.accept_21_18_3_4_1_5013 60 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 171 256 (accept_3_3 59 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 171 256 (Polychromatic418967fa.accept_13_6_2_9_1_1188 58 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 171 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 171 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 171 256 (accept_3_3 56 171 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 171 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 171 256 (accept_3_3 53 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 171 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 171 256 (Polychromatic418967fa.accept_18_15_9_4_1_5185 51 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 171 256 (accept_3_3 50 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 171 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 171 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 171 256 (accept_3_3 47 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 171 256 (Polychromatic418967fa.accept_13_7_2_9_1_1826 46 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 171 256 (Polychromatic418967fa.accept_10_5_1_6_1_672 45 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 171 256 (accept_3_3 44 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 171 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 171 256
  (Polychromatic418967fa.accept_10_2_1_6_1_634 42 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 171 256 (accept_3_3 41 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 171 256 (Polychromatic418967fa.accept_13_1_2_9_1_1186 40 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 171 256 (Polychromatic418967fa.accept_15_9_6_1_1_493 39 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 171 256 (accept_3_3 38 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 171 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 171 256 (accept_3_3 35 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 171 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 171 256 (Polychromatic418967fa.accept_13_7_2_9_1_1826 33 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 171 256 (accept_3_3 32 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 171 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 256
  (Polychromatic418967fa.accept_11_8_6_3_1_661 30 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 171 256 (accept_3_3 29 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 171 256 (Polychromatic418967fa.accept_21_7_3_4_1_14091 28 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 171 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 171 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 171 256 (accept_3_3 26 171 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 256
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 24 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 171 256 (accept_3_3 23 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 171 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 171 256 (Polychromatic418967fa.accept_14_7_3_4_1_1816 21 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 256 (accept_3_3 20 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 171 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 171 256 (accept_3_3 17 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 171 256 (Polychromatic418967fa.accept_13_3_2_9_1_1187 16 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 171 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 171 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 256 (accept_3_3 14 171 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 256
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 171 256 (accept_3_3 11 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 171 256 (Polychromatic418967fa.accept_15_10_6_1_1_3707 10 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 171 256 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 171 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 256 (accept_3_3 8 171 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 171 256 (accept_3_3 5 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  171 256 (Polychromatic418967fa.accept_24_4_3_16_1_2035 4 171 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 171 256 (Polychromatic418967fa.accept_13_3_2_9_1_1187 3 171 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 171 256 (accept_3_3 2 171 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 171 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 170 256
  (Eq.refl Bool.true) (allA_of_3_1 87 170 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 169 256 (Eq.refl
  Bool.true) (allA_succ_of_accept 87 169 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 169 256 (accept_3_3 86 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 169 256 (Polychromatic418967fa.accept_10_5_9_6_1_697 85 169 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 169 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 169 256 (accept_3_3 83 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 169 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 82 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 169 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 169 256 (accept_3_3 80 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 169 256 (Polychromatic418967fa.accept_20_19_9_16_1_2744 79 169 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 169 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 78 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 169 256 (accept_3_3 77 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 169 256 (Polychromatic418967fa.accept_21_13_1_4_1_11182 76 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 169 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 169 256 (accept_3_3 74 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 169 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 169 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 169 256
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 72 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 169 256 (accept_3_3 71 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 169 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 169 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 169 256 (accept_3_3 68 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 169 256 (Polychromatic418967fa.accept_14_11_1_4_1_4445 67 169 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 169 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 66 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 169 256 (accept_3_3 65 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 169 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 169 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 169 256 (accept_3_3 62 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 169 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 169 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 169 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 169 256 (accept_3_3 59 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 169 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 169 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 169 256 (accept_3_3 56 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 169 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 169 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 169 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 169 256 (accept_3_3 53 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 169 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 169 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 169 256 (accept_3_3 50 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 169 256 (Polychromatic418967fa.accept_17_15_16_1_1_7080 49 169 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 169 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 169 256 (accept_3_3 47 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 169 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 169 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 169 256 (accept_3_3 44 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 169 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 43 169 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 169 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 169 256 (accept_3_3 41 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 169 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 169 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 169 256 (accept_3_3 38 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 169 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 169 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 169 256
  (Polychromatic418967fa.accept_17_2_16_1_1_2260 36 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 169 256 (accept_3_3 35 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 169 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 169 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 169 256 (accept_3_3 32 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 169 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 169 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 169 256 (accept_3_3 29 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 169 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 169 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 256 (accept_3_3 26 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 169 256 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 169 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 169 256 (accept_3_3 23 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 256 (accept_3_3 20 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 169 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 256
  (Polychromatic418967fa.accept_11_7_4_3_1_302 18 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 256 (accept_3_3 17 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 256 (Polychromatic418967fa.accept_18_16_7_4_1_3901 16 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 169 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 256 (accept_3_3 14 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 169 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 256 (accept_3_3 11 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 256 (accept_3_3 8 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 256 (Polychromatic418967fa.accept_11_7_4_3_1_302 7 169 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 256 (accept_3_3 5 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 256 (Polychromatic418967fa.accept_22_4_15_14_1_15611 4 169 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 256 (accept_3_3 2 169 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 169 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 168 256
  (Eq.refl Bool.true) (allA_succ_of_gcd 88 168 256 8 11 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 168 256 (Polychromatic418967fa.accept_18_15_6_4_1_5147 87 168
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 168 256 2 43 84 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 168 256
  (Polychromatic418967fa.accept_23_16_7_3_1_10710 85 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 168 256 4 21 42 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 168 256 (accept_3_3 83 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 168 256 2 41 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 168 256 (Polychromatic418967fa.accept_13_3_12_9_1_1193 81 168 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 168 256 8 10 21 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 168 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 79 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 168 256 2 39 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 168 256 (accept_3_3 77 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 168 256 4 19 42 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 168 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 168 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 168 256 2 37 84 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 168 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 73 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 168 256 8 9 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 168 256 (accept_3_3 71 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  168 256 2 35 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 168 256 (Polychromatic418967fa.accept_18_15_6_4_1_5147 69 168 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 168 256 4 17 42 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 168 256
  (Polychromatic418967fa.accept_17_16_15_1_1_11968 67 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 168 256 2 33 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 168 256 (accept_3_3 65 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 168 256 8 8 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 168 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 168 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 168 256 2 31 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 168 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 61
  168 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 168 256 4 15 42 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 168 256 (accept_3_3 59
  168 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 168 256 2 29 84 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 168 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 168 256 8 7 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 168 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 168 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 168 256 2 27 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 168 256 (accept_3_3 53 168 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 168 256 4 13 42 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 168 256 (Polychromatic418967fa.accept_15_6_3_1_1_3678 51 168
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 168 256 2 25 84 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 168 256
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 49 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 168 256 8 6 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 168 256 (accept_3_3 47 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 168 256 2 23 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 168 256 (Polychromatic418967fa.accept_19_7_16_9_1_398 45 168 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 168 256 4 11 42 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 256 2 21 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 168 256 (accept_3_3 41 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 168 256 8 5 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 168 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 168 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 168 256 2 19 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 37
  168 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 168 256 4 9 42 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 168 256 (accept_3_3 35
  168 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 256 2 17 84 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 168 256
  (Polychromatic418967fa.accept_10_3_8_6_1_326 33 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 168 256 8 4 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 168 256 (Polychromatic418967fa.accept_19_12_16_9_1_5976 31 168 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 168 256 2 15 84 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 168 256 (accept_3_3 29 168 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 256 4 7 42 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 168 256 (Polychromatic418967fa.accept_19_8_16_9_1_8847
  27 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 168 256 2 13 84 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 256 8 3 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 168 256 (accept_3_3 23 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  168 256 2 11 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 168 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 168 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 168 256 4 5 42 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 19
  168 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 168 256 2 9 84 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 168 256 (accept_3_3 17
  168 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 256 8 2 21 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 168 256
  (Polychromatic418967fa.accept_18_15_6_4_1_5147 15 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 168 256 2 7 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 168 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 168 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 256 4 3 42 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 256 (accept_3_3 11 168 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 256 2 5 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 168 256 (Polychromatic418967fa.accept_17_9_15_1_1_7048
  9 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 168 256 8 1 21 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 168 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 168 256 2 3 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 168 256 (accept_3_3 5 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168
  256 4 1 42 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  168 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 168 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 168 256 2 1 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 168 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 168 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 167 256
  (Eq.refl Bool.true) (allA_of_3_1 90 167 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 91 166 256 (Eq.refl
  Bool.true) (allA_succ_of_gcd 90 166 256 2 45 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 166 256 (accept_3_3 89 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 166 256 2 44 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 166 256 (Polychromatic418967fa.accept_17_2_13_1_1_3355 87 166 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 166 256 2 43 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 166 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 85 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 166 256 2 42 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 166 256 (accept_3_3 83 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 166 256 2 41 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 166 256 (Polychromatic418967fa.accept_19_5_14_9_1_4554 81 166 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 166 256 2 40 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 166 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 79 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 166 256 2 39 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 166 256 (accept_3_3 77 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 166 256 2 38 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 166 256 (Polychromatic418967fa.accept_21_12_19_4_1_15613 75 166 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 166 256 2 37 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 166 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 166 256 2 36 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 166 256 (accept_3_3 71 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 166 256 2 35 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 166 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 166 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 166 256 2 34 83 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 166 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 166 256 2 33 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 166 256 (accept_3_3 65 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 166 256 2 32 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 166 256 (Polychromatic418967fa.accept_17_12_13_1_1_4478 63 166 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 166 256 2 31 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 166 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 166 256 2 30 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 166 256 (accept_3_3 59 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 166 256 2 29 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 166 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 166 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 166 256 2 28 83 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 166 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 55 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 166 256 2 27 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 166 256 (accept_3_3 53 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 166 256 2 26 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 166 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 166 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 166 256 2 25 83 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 166 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 166 256 2 24 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 166 256 (accept_3_3 47 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 166 256 2 23 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 166 256 (Polychromatic418967fa.accept_13_6_10_9_1_4329 45 166 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 166 256 2 22 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 166 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 166 256 2 21 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 166 256 (accept_3_3 41 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 166 256 2 20 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 166 256 (Polychromatic418967fa.accept_19_1_14_9_1_10155 39 166 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 166 256 2 19 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 166 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 166 256 2 18 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 166 256 (accept_3_3 35 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 166 256 2 17 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 166 256 (Polychromatic418967fa.accept_21_12_19_4_1_15613 33 166 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 166 256 2 16 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 166 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 166 256 2 15 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 166 256 (accept_3_3 29 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 166 256 2 14 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 166 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 166 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 166 256 2 13 83 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 256 2 12 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 256 (accept_3_3 23 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 256 2 11 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 256 (Polychromatic418967fa.accept_20_1_6_16_1_6991 21 166 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 256 2 10 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 256 2 9 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 166 256 (accept_3_3 17 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 166 256 2 8 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 166 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 166 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 166 256 2 7 83 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 166 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 166 256 2 6 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 166 256 (accept_3_3 11 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 166 256 2 5 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 166 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 166 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 256 2 4 83 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 256 2 3 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 256 (accept_3_3 5 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  256 2 2 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 256 (Polychromatic418967fa.accept_19_3_14_9_1_8866 3 166 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 256 2 1 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 166 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 166 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 165 256
  (Eq.refl Bool.true) (allA_succ_of_accept 91 165 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 165 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 90 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 165 256 (accept_3_3 89 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 165 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 165 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 87 165 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 165 256 (accept_3_3 86 165 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 165 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 165 256
  (Polychromatic418967fa.accept_10_4_5_6_1_651 84 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 165 256 (accept_3_3 83 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 165 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 165 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 81 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 165 256 (accept_3_3 80 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 165 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 165 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 165 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 78 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 165 256 (accept_3_3 77 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 165 256 (Polychromatic418967fa.accept_21_13_18_4_1_11181 76 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 165 256 (Polychromatic418967fa.accept_19_18_13_9_1_5971 75 165 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 165 256 (accept_3_3 74 165 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 165 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73
  165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 165 256
  (Polychromatic418967fa.accept_19_15_13_9_1_7324 72 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 165 256 (accept_3_3 71 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 165 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 165 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 165 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 165 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 165 256 (accept_3_3 68 165 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 165 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67
  165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 165 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 66 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 165 256 (accept_3_3 65 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 165 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 165 256 (Polychromatic418967fa.accept_14_7_11_4_1_3455 63 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 165 256 (accept_3_3 62 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 165 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 165 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 165 256 (accept_3_3 59 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 165 256 (Polychromatic418967fa.accept_20_18_5_16_1_5425 58 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 165 256 (Polychromatic418967fa.accept_14_1_11_4_1_3430 57 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 165 256 (accept_3_3 56 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 165 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 165 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 165 256
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 165 256 (accept_3_3 53 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 165 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 165 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 165 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 165 256 (accept_3_3 50 165 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 256
  (Polychromatic418967fa.accept_19_10_13_9_1_4552 48 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 165 256 (accept_3_3 47 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 165 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 165 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 165 256 (Polychromatic418967fa.accept_19_7_13_9_1_10179 45 165
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 165 256 (accept_3_3 44 165
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 165 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 165 256 (accept_3_3 41 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 165 256 (Polychromatic418967fa.accept_17_6_12_1_1_7043 40 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 165 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 39 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 165 256 (accept_3_3 38 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 165 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 256
  (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 165 256 (accept_3_3 35 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 165 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 165 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 165 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 165 256 (accept_3_3 32 165 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 165 256 (accept_3_3 29 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 165 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 165 256 (Polychromatic418967fa.accept_21_6_18_4_1_4952 27 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 256 (accept_3_3 26 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 165 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 165 256 (accept_3_3 23 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 165 256 (Polychromatic418967fa.accept_14_8_11_4_1_3438 22 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 165 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 256 (accept_3_3 20 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 165 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 165 256 (accept_3_3 17 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 165 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 165 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 165 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 256 (accept_3_3 14 165 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 256
  (Polychromatic418967fa.accept_21_12_18_4_1_4955 12 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 165 256 (accept_3_3 11 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 165 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 165 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 165 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 256 (accept_3_3 8 165 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 165 256 (accept_3_3 5 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  165 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 165 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 165 256 (Polychromatic418967fa.accept_19_3_13_9_1_8876 3 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 256 (accept_3_3 2 165 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 165 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 164 256
  (Eq.refl Bool.true) (allA_of_3_1 93 164 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 94 163 256 (Eq.refl
  Bool.true) (allA_succ_of_accept 93 163 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 163 256 (accept_3_3 92 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 163 256 (Polychromatic418967fa.accept_19_15_11_9_1_11629 91 163 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 163 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 90 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 163 256 (accept_3_3 89 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 163 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 163 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 163 256 (accept_3_3 86 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 163 256 (Polychromatic418967fa.accept_15_10_13_1_1_3698 85 163 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 163 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 84 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 163 256 (accept_3_3 83 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 163 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 82 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 163 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 163 256 (accept_3_3 80 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 163 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 163 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 163 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 78 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 163 256 (accept_3_3 77 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 163 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 163 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 163 256 (accept_3_3 74 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 163 256 (Polychromatic418967fa.accept_13_8_7_9_1_611 73 163 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 163 256
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 72 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 163 256 (accept_3_3 71 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 163 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 163 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 163 256 (accept_3_3 68 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 163 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 67 163 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 163 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 163 256 (accept_3_3 65 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 163 256 (Polychromatic418967fa.accept_19_7_11_9_1_2139 64 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 163 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 163 256 (accept_3_3 62 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 163 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 163 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 163 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 163 256 (accept_3_3 59 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 163 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 163 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 163 256 (accept_3_3 56 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 163 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 163 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 163 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 163 256 (accept_3_3 53 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 163 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 163 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 163 256 (accept_3_3 50 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 163 256 (Polychromatic418967fa.accept_10_9_3_6_1_686 49 163 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 163 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 163 256 (accept_3_3 47 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 163 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 163 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 163 256 (accept_3_3 44 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 163 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 163 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 163 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 163 256 (accept_3_3 41 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 163 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 163 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 163 256 (accept_3_3 38 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 163 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 37 163 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 163 256
  (Polychromatic418967fa.accept_19_17_11_9_1_2141 36 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 163 256 (accept_3_3 35 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 163 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 163 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 163 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 163 256 (accept_3_3 32 163 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 163 256
  (Polychromatic418967fa.accept_17_14_10_1_1_4523 31 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 163 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 256 (accept_3_3 29 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 163 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 256 (accept_3_3 26 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 163 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 256 (accept_3_3 23 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 163 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 256 (accept_3_3 20 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 163 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 256 (accept_3_3 17 163 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 163 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 256 (accept_3_3 14 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 256 (accept_3_3 11 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 163 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 256 (accept_3_3 8 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 256 (accept_3_3 5 163 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 256 (Polychromatic418967fa.accept_13_4_7_9_1_5260 4 163 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 256 (accept_3_3 2 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 256 (Polychromatic418967fa.accept_19_1_11_9_1_10307 1 163 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 162
  256 (Eq.refl Bool.true) (allA_succ_of_gcd 94 162 256 2 47 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 162 256 (Polychromatic418967fa.accept_11_5_8_3_1_66 93 162 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 162 256 2 46 81 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 162 256
  (Polychromatic418967fa.accept_10_1_2_6_1_638 91 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 162 256 2 45 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 162 256 (accept_3_3 89 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 162 256 2 44 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 162 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 162 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 162 256 2 43 81 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 162 256
  (Polychromatic418967fa.accept_13_7_6_9_1_1831 85 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 162 256 2 42 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 162 256 (accept_3_3 83 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 162 256 2 41 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 162 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 162 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 162 256 2 40 81 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 162 256
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 79 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 162 256 2 39 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 162 256 (accept_3_3 77 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 162 256 2 38 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 162 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 162 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 162 256 2 37 81 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 162 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 73 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 162 256 2 36 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 162 256 (accept_3_3 71 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 162 256 2 35 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 162 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 162 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 162 256 2 34 81 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 162 256
  (Polychromatic418967fa.accept_13_2_6_9_1_2636 67 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 162 256 2 33 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 162 256 (accept_3_3 65 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 162 256 2 32 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 162 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 162 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 162 256 2 31 81 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 162 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 162 256 2 30 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 162 256 (accept_3_3 59 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 162 256 2 29 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 162 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 162 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 162 256 2 28 81 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 162 256
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 55 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 256 2 27 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 162 256 (accept_3_3 53 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 162 256 2 26 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 162 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 51 162 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 162 256 2 25 81 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 162 256
  (Polychromatic418967fa.accept_11_5_8_3_1_66 49 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 256 2 24 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 162 256 (accept_3_3 47 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 162 256 2 23 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 162 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 162 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 162 256 2 22 81 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 256
  (Polychromatic418967fa.accept_13_4_6_9_1_3401 43 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 256 2 21 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 162 256 (accept_3_3 41 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 162 256 2 20 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 162 256 (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 162 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 162 256 2 19 81 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 162 256
  (Polychromatic418967fa.accept_17_3_9_1_1_1344 37 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 256 2 18 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 256 (accept_3_3 35 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 162 256 2 17 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 162 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 162 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 162 256 2 16 81 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 256 2 15 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 256 (accept_3_3 29 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 162 256 2 14 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 162 256 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 162 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 162 256 2 13 81 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 256
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 25 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 256 2 12 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 256 (accept_3_3 23 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 162 256 2 11 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 162 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 162 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 162 256 2 10 81 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 256 2 9 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 256 (accept_3_3 17 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 162 256 2 8 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 162 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 162 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 162 256 2 7 81 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 256
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 162 256 2 6 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 162 256 (accept_3_3 11 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 162 256 2 5 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 162 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 162 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 162 256 2 4 81 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 256
  (Polychromatic418967fa.accept_13_7_6_9_1_1831 7 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 256 2 3 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 256 (accept_3_3 5 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162
  256 2 2 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  162 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 162 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 162 256 2 1 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 162 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 162 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 161
  256 (Eq.refl Bool.true) (allA_of_3_1 96 161 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 97 160 256
  (Eq.refl Bool.true) (allA_succ_of_gcd 96 160 256 32 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 160 256 (accept_3_3 95 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 160 256 2 47 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 160 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 93 160 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 160 256 4 23 40 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 160 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 91 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 160 256 2 45 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 160 256 (accept_3_3 89 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 160 256 8 11 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 160 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 160 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 160 256 2 43 80 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 160 256
  (Polychromatic418967fa.accept_11_8_6_3_1_661 85 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 160 256 4 21 40 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 160 256 (accept_3_3 83 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 160 256 2 41 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 160 256 (Polychromatic418967fa.accept_15_6_10_1_1_3675 81 160 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 160 256 16 5 10 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 160 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 79 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 160 256 2 39 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 160 256 (accept_3_3 77 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 160 256 4 19 40 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 160 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 160 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 160 256 2 37 80 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 160 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 73 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 160 256 8 9 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 160 256 (accept_3_3 71 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  160 256 2 35 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 160 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 69 160 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 160 256 4 17 40 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 160 256 (Polychromatic418967fa.accept_15_7_10_1_1_1836
  67 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 160 256 2 33 80 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 160 256
  (accept_3_3 65 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 160 256 32 2 5 8 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 160 256
  (Polychromatic418967fa.accept_11_8_6_3_1_661 63 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 160 256 2 31 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 160 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 160 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 160 256 4 15 40 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 160 256 (accept_3_3 59 160 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 160 256 2 29 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 160 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 57
  160 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 160 256 8 7 20 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 160 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 55 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 160 256 2 27 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 160 256 (accept_3_3 53 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 160 256 4 13 40 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 160 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 160 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 160 256 2 25 80 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 160 256
  (Polychromatic418967fa.accept_19_11_8_9_1_5993 49 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 160 256 16 3 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 160 256 (accept_3_3 47 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 160 256 2 23 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 160 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 160 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 160 256 4 11 40 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 160 256
  (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 160 256 2 21 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 160 256 (accept_3_3 41 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 160 256 8 5 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 160 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 160 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 160 256 2 19 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 160 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 37
  160 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 160 256 4 9 40 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 160 256 (accept_3_3 35
  160 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 160 256 2 17 80 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 160 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 160 256 32 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 160 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 160 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 160 256 2 15 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 160 256 (accept_3_3 29 160 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 160 256 4 7 40 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 160 256 (Polychromatic418967fa.accept_17_10_7_1_1_7024 27 160
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 160 256 2 13 80 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 160 256
  (Polychromatic418967fa.accept_17_8_7_1_1_4521 25 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 160 256 8 3 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 160 256 (accept_3_3 23 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  160 256 2 11 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 160 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 160 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 256 4 5 40 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 19
  160 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 160 256 2 9 80 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 160 256 (accept_3_3 17
  160 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 160 256 16 1 10 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 160 256
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 160 256 2 7 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 160 256 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 160 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 160 256 4 3 40 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 160 256 (accept_3_3 11 160 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 160 256 2 5 80 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 160 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 160 256 8 1 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 160 256 (Polychromatic418967fa.accept_13_7_4_9_1_1865 7 160 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 256 2 3 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 160 256 (accept_3_3 5 160 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160 256 4 1 40 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 160 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 160 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 160 256 2 1 80 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 160 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 1 160 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 160 256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 98 159 256 (Eq.refl Bool.true) (allA_succ_of_accept 97 159 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  97 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 159 256
  (Polychromatic418967fa.accept_11_8_5_3_1_694 96 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 159 256 (accept_3_3 95 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 159 256 (Polychromatic418967fa.accept_25_19_9_6_1_10439 94 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 159 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 93 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 159 256 (accept_3_3 92 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 159 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 159 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 90 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 159 256 (accept_3_3 89 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 159 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 88 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 159 256 (Polychromatic418967fa.accept_17_2_6_1_1_8357 87 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 159 256 (accept_3_3 86 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 159 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 159 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 159 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 159 256 (accept_3_3 83 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 159 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 159 256 (Polychromatic418967fa.accept_15_6_9_1_1_1823 81 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 159 256 (accept_3_3 80 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 159 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 159 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 159 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 78 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 159 256 (accept_3_3 77 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 159 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 159 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 159 256 (accept_3_3 74 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 159 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 72 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 159 256 (accept_3_3 71 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 159 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 159 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 159 256 (accept_3_3 68 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 159 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 159 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 159 256 (accept_3_3 65 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 159 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 159 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 63 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 159 256 (accept_3_3 62 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 159 256
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 60 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 159 256 (accept_3_3 59 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 159 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 159 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 159 256 (accept_3_3 56 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 159 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 159 256 (accept_3_3 53 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 159 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 159 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 256 (accept_3_3 50 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 159 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 159 256 (accept_3_3 47 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 159 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 159 256 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 256 (accept_3_3 44 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 159 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 159 256 (accept_3_3 41 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 159 256 (Polychromatic418967fa.accept_15_10_9_1_1_3688 40 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 159 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 256 (accept_3_3 38 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 159 256 (accept_3_3 35 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 159 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 159 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 33 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 256 (accept_3_3 32 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 159 256 (accept_3_3 29 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 159 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 159 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 256 (accept_3_3 26 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 256
  (Polychromatic418967fa.accept_18_6_15_4_1_3916 24 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 159 256 (accept_3_3 23 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 159 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 159 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 256 (accept_3_3 20 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 159 256 (accept_3_3 17 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 159 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 159 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 256 (accept_3_3 14 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 159 256 (accept_3_3 11 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 159 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 159 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 256 (accept_3_3 8 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 159 256 (accept_3_3 5 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  159 256 (Polychromatic418967fa.accept_24_4_15_16_1_12158 4 159 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 159 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 256 (accept_3_3 2 159 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 159 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  158 256 (Eq.refl Bool.true) (allA_of_3_1 99 158 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 100 157 256
  (Eq.refl Bool.true) (allA_succ_of_accept 99 157 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 99 157 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 157 256 (accept_3_3 98 157 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 157 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 97 157 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 157 256
  (Polychromatic418967fa.accept_13_5_1_9_1_618 96 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 157 256 (accept_3_3 95 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 157 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 94 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 157 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 157 256 (accept_3_3 92 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 157 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 91 157 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 157 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 90 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 157 256 (accept_3_3 89 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 157 256 (Polychromatic418967fa.accept_13_10_1_9_1_3380 88 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 157 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 157 256 (accept_3_3 86 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 157 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 85 157 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 157 256
  (Polychromatic418967fa.accept_13_6_1_9_1_619 84 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 157 256 (accept_3_3 83 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 157 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 82 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 157 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 157 256 (accept_3_3 80 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 157 256 (Polychromatic418967fa.accept_18_7_13_4_1_1670 79 157 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 157 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 78 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 157 256 (accept_3_3 77 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 157 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 157 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 157 256 (accept_3_3 74 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 157 256 (Polychromatic418967fa.accept_10_3_7_6_1_659 73 157 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 157 256
  (Polychromatic418967fa.accept_19_15_5_9_1_3299 72 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 157 256 (accept_3_3 71 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 157 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 157 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 157 256 (accept_3_3 68 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 157 256 (Polychromatic418967fa.accept_13_2_1_9_1_1174 67 157 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 157 256
  (Polychromatic418967fa.accept_15_6_7_1_1_93 66 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 157 256 (accept_3_3 65 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 157 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 157 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 157 256 (accept_3_3 62 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 157 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 61 157 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 157 256
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 60 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 157 256 (accept_3_3 59 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 157 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 157 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 157 256 (accept_3_3 56 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 157 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 157 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 157 256
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 54 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 157 256 (accept_3_3 53 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 157 256 (Polychromatic418967fa.accept_19_14_5_9_1_4596 52 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 157 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 157 256 (accept_3_3 50 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 157 256 (Polychromatic418967fa.accept_13_10_1_9_1_3380 49 157 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 157 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 157 256 (accept_3_3 47 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 157 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 157 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 157 256 (accept_3_3 44 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 157 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 157 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 157 256
  (Polychromatic418967fa.accept_17_8_4_1_1_5730 42 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 157 256 (accept_3_3 41 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 157 256 (Polychromatic418967fa.accept_15_10_7_1_1_3686 40 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 157 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 157 256 (accept_3_3 38 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 157 256 (Polychromatic418967fa.accept_13_11_1_9_1_1179 37 157 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 157 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 157 256 (accept_3_3 35 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 157 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 157 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 157 256 (accept_3_3 32 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 157 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 31 157 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 157 256
  (Polychromatic418967fa.accept_23_7_19_3_1_12427 30 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 157 256 (accept_3_3 29 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 157 256 (Polychromatic418967fa.accept_13_2_1_9_1_1174 28 157 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 157 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 157 256 (accept_3_3 26 157 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 256
  (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 157 256 (Polychromatic418967fa.accept_13_11_1_9_1_1179 24 157 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 256 (accept_3_3 23 157 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 157 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21
  157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 256 (accept_3_3 20
  157 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 256
  (Polychromatic418967fa.accept_13_6_1_9_1_619 19 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 157 256 (Polychromatic418967fa.accept_13_5_1_9_1_618 18 157 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 256 (accept_3_3 17 157 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 157 256 (Polychromatic418967fa.accept_21_16_10_4_1_3433 16 157 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 256 (accept_3_3 14 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 256 (Polychromatic418967fa.accept_19_12_5_9_1_7320 12 157 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 256 (accept_3_3 11 157 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 157
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 256 (accept_3_3 8 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 256 (Polychromatic418967fa.accept_14_7_3_4_1_1816 7 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 256 (accept_3_3 5 157 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 256 (Polychromatic418967fa.accept_19_4_5_9_1_8855 4 157 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 256 (accept_3_3 2 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 157 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 156 256 (Eq.refl Bool.true) (allA_succ_of_gcd 100 156 256 4 25 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 156 256 (Polychromatic418967fa.accept_15_9_6_1_1_493
  99 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 156 256 2 49 78 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 156 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 97 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 156 256 4 24 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 156 256 (accept_3_3 95 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 156 256 2 47 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 156 256 (Polychromatic418967fa.accept_14_9_2_4_1_1814 93 156 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 156 256 4 23 39 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 156 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 91 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 156 256 2 45 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 156 256 (accept_3_3 89 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 156 256 4 22 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 156 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 87 156 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 156 256 2 43 78 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 156 256
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 85 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 156 256 4 21 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 156 256 (accept_3_3 83 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 156 256 2 41 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 156 256 (Polychromatic418967fa.accept_18_9_12_4_1_1659 81 156 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 156 256 4 20 39 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 156 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 79 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 156 256 2 39 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 156 256 (accept_3_3 77 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 156 256 4 19 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 156 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 156 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 156 256 2 37 78 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 156 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 73 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 156 256 4 18 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 156 256 (accept_3_3 71 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 156 256 2 35 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 156 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 156 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 156 256 4 17 39 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 156 256
  (Polychromatic418967fa.accept_11_1_2_3_1_688 67 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 156 256 2 33 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 156 256 (accept_3_3 65 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 156 256 4 16 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 156 256 (Polychromatic418967fa.accept_15_3_6_1_1_1834 63 156 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 156 256 2 31 78 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 156 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 61 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 256 4 15 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 256 (accept_3_3 59 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 156 256 2 29 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 156 256 (Polychromatic418967fa.accept_17_6_3_1_1_7011 57 156 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 156 256 4 14 39 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 156 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 256 2 27 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 256 (accept_3_3 53 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 156 256 4 13 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 156 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 156 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 156 256 2 25 78 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 156 256
  (Polychromatic418967fa.accept_17_15_3_1_1_9696 49 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 256 4 12 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 256 (accept_3_3 47 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 156 256 2 23 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 156 256 (Polychromatic418967fa.accept_11_1_2_3_1_688 45 156 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 156 256 4 11 39 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 156 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 256 2 21 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 256 (accept_3_3 41 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 156 256 4 10 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 156 256 (Polychromatic418967fa.accept_15_9_6_1_1_493 39 156 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 156 256 2 19 78 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 256 4 9 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 156 256 (accept_3_3 35 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  156 256 2 17 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 156 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 156 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 156 256 4 8 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 256
  (Polychromatic418967fa.accept_23_8_18_3_1_15642 31 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 156 256 2 15 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 156 256 (accept_3_3 29 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 156 256 4 7 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 156 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 156 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 156 256 2 13 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 25
  156 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 256 4 6 39 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 256 (accept_3_3 23
  156 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 256 2 11 78 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 256
  (Polychromatic418967fa.accept_19_2_4_9_1_1131 21 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 156 256 4 5 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 156 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 156 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 256 2 9 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 256 (accept_3_3 17 156 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 256 4 4 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 156 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 156 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 156 256 2 7 78 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 156 256 4 3 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 156 256 (accept_3_3 11 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  156 256 2 5 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 156 256 (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 156 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 156 256 4 2 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 156 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 256 2 3 78 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 256 (accept_3_3 5
  156 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 256 4 1 39 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 156 256
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 3 156 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 156 256 2 1 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 156 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 156 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 156
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 155 256 (Eq.refl Bool.true) (allA_of_3_1 102 155 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 103 154
  256 (Eq.refl Bool.true) (allA_succ_of_gcd 102 154 256 2 51 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 154 256 (accept_3_3 101 154 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 154 256 2 50 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 154 256 (Polychromatic418967fa.accept_13_8_11_9_1_593 99 154 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 154 256 2 49 77 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 154 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 97 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 154 256 2 48 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 154 256 (accept_3_3 95 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 154 256 2 47 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 154 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 93 154 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 154 256 2 46 77 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 154 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 91 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 154 256 2 45 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 154 256 (accept_3_3 89 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 154 256 2 44 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 154 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 87 154 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 154 256 2 43 77 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 154 256
  (Polychromatic418967fa.accept_10_5_4_6_1_319 85 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 154 256 2 42 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 154 256 (accept_3_3 83 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 154 256 2 41 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 154 256 (Polychromatic418967fa.accept_21_18_7_4_1_8131 81 154 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 154 256 2 40 77 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 154 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 79 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 154 256 2 39 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 154 256 (accept_3_3 77 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 154 256 2 38 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 154 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 75 154 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 154 256 2 37 77 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 154 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 154 256 2 36 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 154 256 (accept_3_3 71 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 154 256 2 35 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 154 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 154 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 154 256 2 34 77 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 154 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 154 256 2 33 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 154 256 (accept_3_3 65 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 154 256 2 32 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 154 256 (Polychromatic418967fa.accept_15_3_4_1_1_1072 63 154 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 154 256 2 31 77 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 154 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 61 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 154 256 2 30 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 154 256 (accept_3_3 59 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 154 256 2 29 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 154 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 154 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 154 256 2 28 77 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 154 256
  (Polychromatic418967fa.accept_10_5_4_6_1_319 55 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 154 256 2 27 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 154 256 (accept_3_3 53 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 154 256 2 26 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 154 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 154 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 154 256 2 25 77 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 154 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 154 256 2 24 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 154 256 (accept_3_3 47 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 154 256 2 23 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 154 256 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 154 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 154 256 2 22 77 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 154 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 43 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 154 256 2 21 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 154 256 (accept_3_3 41 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 154 256 2 20 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 154 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 154 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 154 256 2 19 77 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 154 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 154 256 2 18 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 154 256 (accept_3_3 35 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 154 256 2 17 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 154 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 154 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 154 256 2 16 77 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 154 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 154 256 2 15 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 154 256 (accept_3_3 29 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 154 256 2 14 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 154 256 (Polychromatic418967fa.accept_13_1_11_9_1_1857 27 154 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 256 2 13 77 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 154 256 2 12 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 154 256 (accept_3_3 23 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 256 2 11 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 154 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 154 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 256 2 10 77 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 154 256 2 9 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 154 256 (accept_3_3 17 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 154 256 2 8 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 154 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 154 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 154 256 2 7 77 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 154 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 154 256 2 6 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 154 256 (accept_3_3 11 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 154 256 2 5 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 154 256 (Polychromatic418967fa.accept_23_9_16_3_1_12408 9 154 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 154 256 2 4 77 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 154 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 154 256 2 3 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 154 256 (accept_3_3 5 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154
  256 2 2 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  154 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 154 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 154 256 2 1 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 154 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 154 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 153 256 (Eq.refl Bool.true) (allA_succ_of_accept 103 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 153 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 153 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 102 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 153 256 (accept_3_3 101 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 153 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 100 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 153 256 (Polychromatic418967fa.accept_10_9_3_6_1_686 99 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 153 256 (accept_3_3 98 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 153 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 153 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 96 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 153 256 (accept_3_3 95 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 153 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 94 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 153 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 93 153 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 153 256 (accept_3_3 92 153 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 153 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 90 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 153 256 (accept_3_3 89 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 153 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 88 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 153 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 153 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 153 256 (accept_3_3 86 153 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 153 256
  (Polychromatic418967fa.accept_11_7_10_3_1_633 84 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 153 256 (accept_3_3 83 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 153 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 82 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 153 256 (Polychromatic418967fa.accept_15_6_3_1_1_3678 81 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 153 256 (accept_3_3 80 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 153 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 153 256
  (Polychromatic418967fa.accept_10_8_3_6_1_685 78 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 153 256 (accept_3_3 77 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 153 256 (Polychromatic418967fa.accept_21_13_6_4_1_2178 76 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 153 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 153 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 153 256 (accept_3_3 74 153 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 153 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 153 256 (accept_3_3 71 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 153 256 (Polychromatic418967fa.accept_21_7_6_4_1_3445 70 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 153 256 (Polychromatic418967fa.accept_10_9_3_6_1_686 69 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 153 256 (accept_3_3 68 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 153 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 153 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 66 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 153 256 (accept_3_3 65 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 153 256 (Polychromatic418967fa.accept_13_12_10_9_1_1166 64 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 153 256 (Polychromatic418967fa.accept_20_3_13_16_1_641 63 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 153 256 (accept_3_3 62 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 153 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 153 256
  (Polychromatic418967fa.accept_21_18_6_4_1_5031 60 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 153 256 (accept_3_3 59 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 153 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 153 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 57 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 256 (accept_3_3 56 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 153 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 153 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 153 256 (accept_3_3 53 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 153 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 153 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 153 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 256 (accept_3_3 50 153 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 153 256
  (Polychromatic418967fa.accept_10_8_3_6_1_685 48 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 153 256 (accept_3_3 47 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 153 256 (Polychromatic418967fa.accept_19_8_1_9_1_7329 46 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 153 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 153 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 256 (accept_3_3 44 153 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 153 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 153 256 (accept_3_3 41 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 153 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 153 256 (Polychromatic418967fa.accept_10_9_3_6_1_686 39 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 256 (accept_3_3 38 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 153 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 256
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 153 256 (accept_3_3 35 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 153 256 (Polychromatic418967fa.accept_15_4_3_1_1_487 34 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 153 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 153 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 256 (accept_3_3 32 153 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 153 256 (accept_3_3 29 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 153 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 153 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 256 (accept_3_3 26 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 153 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 153 256 (accept_3_3 23 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 153 256 (Polychromatic418967fa.accept_24_22_9_16_1_12204 22 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 256 (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 256 (accept_3_3 20 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 153 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 256
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 153 256 (accept_3_3 17 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 153 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 153 256 (Polychromatic418967fa.accept_18_15_9_4_1_5185 15 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 256 (accept_3_3 14 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 153 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 153 256 (accept_3_3 11 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 153 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 153 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 153 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 256 (accept_3_3 8 153 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 153 256 (accept_3_3 5 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  153 256 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 153 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 153 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 153 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 256 (accept_3_3 2 153 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 153 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 152 256 (Eq.refl Bool.true) (allA_of_3_1 105 152 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 106 151 256 (Eq.refl Bool.true) (allA_succ_of_accept 105 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 151 256 (accept_3_3 104 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 151 256 (Polychromatic418967fa.accept_13_12_8_9_1_1833 103 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 151 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 102 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 151 256 (accept_3_3 101 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 151 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 100 151
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 151 256 (accept_3_3 98 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 151 256 (Polychromatic418967fa.accept_10_7_1_6_1_673 97 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 151 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 96 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 151 256 (accept_3_3 95 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 151 256 (Polychromatic418967fa.accept_11_6_8_3_1_2236 94 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 151 256 (accept_3_3 92 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 151 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 151 256 (Polychromatic418967fa.accept_13_12_8_9_1_1833 90 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 151 256 (accept_3_3 89 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 151 256 (Polychromatic418967fa.accept_17_3_15_1_1_3348 88 151
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 151 256 (accept_3_3 86 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 151 256 (Polychromatic418967fa.accept_10_5_1_6_1_672 85 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 151 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 151 256 (accept_3_3 83 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 151 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 151 256 (accept_3_3 80 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 151 256 (Polychromatic418967fa.accept_13_1_8_9_1_1154 79 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 151 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 78 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 151 256 (accept_3_3 77 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 151 256 (Polychromatic418967fa.accept_13_11_8_9_1_1161 76 151 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 151 256 (accept_3_3 74 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 151 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 151 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 72 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 151 256 (accept_3_3 71 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 151 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 151
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 151 256 (accept_3_3 68 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 151 256 (Polychromatic418967fa.accept_10_7_1_6_1_673 67 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 151 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 151 256 (accept_3_3 65 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 151 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 151 256 (accept_3_3 62 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 151 256 (Polychromatic418967fa.accept_11_6_8_3_1_2236 61 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 151 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 151 256 (accept_3_3 59 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 151 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 151 256 (accept_3_3 56 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 151 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 151 256 (Polychromatic418967fa.accept_17_3_15_1_1_3348 54 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 256 (accept_3_3 53 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 151 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 151
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 151 256 (accept_3_3 50 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 151 256 (Polychromatic418967fa.accept_11_5_8_3_1_66 49 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 151 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 151 256 (accept_3_3 47 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 151 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 151 256 (accept_3_3 44 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 151 256 (Polychromatic418967fa.accept_13_4_8_9_1_1156 43 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 151 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 256 (accept_3_3 41 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 256 (Polychromatic418967fa.accept_13_1_8_9_1_1154 40 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 256 (accept_3_3 38 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 256 (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 256 (accept_3_3 35 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 151
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 256 (accept_3_3 32 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 256 (Polychromatic418967fa.accept_18_13_7_4_1_2738 31 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 256 (accept_3_3 29 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 256 (accept_3_3 26 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 256 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 256 (accept_3_3 23 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 256 (accept_3_3 20 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 256 (Polychromatic418967fa.accept_20_18_11_16_1_6973 18 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 256 (accept_3_3 17 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 256 (Polychromatic418967fa.accept_11_5_8_3_1_66 16 151 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 256 (accept_3_3 14 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 256 (Polychromatic418967fa.accept_18_13_7_4_1_2738 13 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 256 (accept_3_3 11 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 256 (accept_3_3 8 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 256 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 256 (accept_3_3 5 151 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 256 (Polychromatic418967fa.accept_13_4_8_9_1_1156 4 151 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 256 (accept_3_3 2 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 151 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 150 256 (Eq.refl Bool.true) (allA_succ_of_gcd 106 150 256 2 53 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 150 256
  (Polychromatic418967fa.accept_12_9_6_4_1_402 105 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 150 256 2 52 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 150 256 (Polychromatic418967fa.accept_11_4_7_3_1_289 103 150 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 150 256 2 51 75 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 150 256 (accept_3_3 101 150 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 150 256 2 50 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 150 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 99 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 150 256 2 49 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 150 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 97 150 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 150 256 2 48 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 150 256 (accept_3_3 95 150 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 150 256 2 47 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 150 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 93
  150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 150 256 2 46 75 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 150 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 91 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 150 256 2 45 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 150 256 (accept_3_3 89 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 150 256 2 44 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 150 256 (Polychromatic418967fa.accept_11_10_7_3_1_3679 87 150 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 150 256 2 43 75 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 150 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 85 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 150 256 2 42 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 150 256 (accept_3_3 83 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 150 256 2 41 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 150 256 (Polychromatic418967fa.accept_11_4_7_3_1_289 81 150 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 150 256 2 40 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 150 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 79 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 150 256 2 39 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 150 256 (accept_3_3 77 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 150 256 2 38 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 150 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 150 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 150 256 2 37 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 150 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 73 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 150 256 2 36 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 150 256 (accept_3_3 71 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 150 256 2 35 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 150 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 150 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 150 256 2 34 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 150 256
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 67 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 150 256 2 33 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 150 256 (accept_3_3 65 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 150 256 2 32 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 150 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 150 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 150 256 2 31 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 150 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 61 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 256 2 30 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 256 (accept_3_3 59 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 150 256 2 29 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 150 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 150 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 150 256 2 28 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 150 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 55 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 150 256 2 27 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 150 256 (accept_3_3 53 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 150 256 2 26 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 150 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 150 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 150 256 2 25 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 150 256
  (Polychromatic418967fa.accept_14_7_10_4_1_130 49 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 256 2 24 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 256 (accept_3_3 47 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 150 256 2 23 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 150 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 150 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 150 256 2 22 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 256 2 21 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 256 (accept_3_3 41 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 150 256 2 20 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 150 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 150 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 150 256 2 19 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 37 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 256 2 18 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 256 (accept_3_3 35 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 150 256 2 17 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 150 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 150 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 150 256 2 16 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 256
  (Polychromatic418967fa.accept_29_2_5_24_1_15641 31 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 150 256 2 15 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 150 256 (accept_3_3 29 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 150 256 2 14 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 150 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 150 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 150 256 2 13 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 150 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 256 2 12 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 256 (accept_3_3 23 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 150 256 2 11 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 150 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 150 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 150 256 2 10 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 19 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 256 2 9 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 150 256 (accept_3_3 17 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 150 256 2 8 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 150 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 150 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 150 256 2 7 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 256 2 6 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 150 256 (accept_3_3 11 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 256 2 5 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 150 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 150 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 150 256 2 4 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 150 256 2 3 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 150 256 (accept_3_3 5 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150
  256 2 2 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  150 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 150 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 150 256 2 1 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 150 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 150 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 149 256 (Eq.refl Bool.true) (allA_of_3_1 108 149 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 109 148 256 (Eq.refl Bool.true) (allA_succ_of_gcd 108 148 256 4 27 37 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 148 256 (accept_3_3 107 148 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 148 256 2 53 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 148 256 (Polychromatic418967fa.accept_13_1_5_9_1_226
  105 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 148 256 4 26 37 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 148 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 103 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 148 256 2 51 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 148 256 (accept_3_3 101 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 148 256 4 25 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 148 256 (Polychromatic418967fa.accept_19_4_15_9_1_8845 99 148 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 148 256 2 49 74 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 148 256
  (Polychromatic418967fa.accept_19_2_15_9_1_7318 97 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 148 256 4 24 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 148 256 (accept_3_3 95 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 148 256 2 47 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 148 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 93 148 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 148 256 4 23 37 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 148 256
  (Polychromatic418967fa.accept_17_6_12_1_1_7043 91 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 148 256 2 45 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 148 256 (accept_3_3 89 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 148 256 4 22 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 148 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 148 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 148 256 2 43 74 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 148 256
  (Polychromatic418967fa.accept_11_8_5_3_1_694 85 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 148 256 4 21 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 148 256 (accept_3_3 83 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 148 256 2 41 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 148 256 (Polychromatic418967fa.accept_13_3_5_9_1_5285 81 148 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 148 256 4 20 37 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 148 256
  (Polychromatic418967fa.accept_13_1_5_9_1_226 79 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 148 256 2 39 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 148 256 (accept_3_3 77 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 148 256 4 19 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 148 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 148 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 148 256 2 37 74 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 148 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 73 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 148 256 4 18 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 148 256 (accept_3_3 71 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 148 256 2 35 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 148 256 (Polychromatic418967fa.accept_13_4_5_9_1_1829 69 148 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 148 256 4 17 37 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 148 256
  (Polychromatic418967fa.accept_13_2_5_9_1_610 67 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 148 256 2 33 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 148 256 (accept_3_3 65 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 148 256 4 16 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 148 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 148 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 148 256 2 31 74 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 148 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 148 256 4 15 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 148 256 (accept_3_3 59 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 148 256 2 29 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 148 256 (Polychromatic418967fa.accept_15_12_13_1_1_3695 57 148 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 148 256 4 14 37 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 148 256
  (Polychromatic418967fa.accept_13_3_5_9_1_5285 55 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 148 256 2 27 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 148 256 (accept_3_3 53 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 148 256 4 13 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 148 256 (Polychromatic418967fa.accept_19_13_15_9_1_3293 51 148 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 148 256 2 25 74 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 148 256
  (Polychromatic418967fa.accept_17_15_12_1_1_3365 49 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 148 256 4 12 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 148 256 (accept_3_3 47 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 148 256 2 23 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 148 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 148 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 148 256 4 11 37 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 148 256
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 148 256 2 21 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 148 256 (accept_3_3 41 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 148 256 4 10 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 148 256 (Polychromatic418967fa.accept_14_11_8_4_1_2628 39 148 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 256 2 19 74 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 256
  (Polychromatic418967fa.accept_19_18_15_9_1_3310 37 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 148 256 4 9 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 148 256 (accept_3_3 35 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 148 256 2 17 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 148 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 148 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 256 4 8 37 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 148 256 2 15 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 148 256 (accept_3_3 29 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 148 256 4 7 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 148 256 (Polychromatic418967fa.accept_13_1_5_9_1_226 27 148 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 148 256 2 13 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 256 (Polychromatic418967fa.accept_14_11_8_4_1_2628
  25 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 148 256 4 6 37 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 148 256
  (accept_3_3 23 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 148 256 2 11 74 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 148 256
  (Polychromatic418967fa.accept_19_2_15_9_1_7318 21 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 148 256 4 5 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 148 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 148 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 148 256 2 9 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 148 256 (accept_3_3 17 148 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 148 256 4 4 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 148 256 (Polychromatic418967fa.accept_13_2_5_9_1_610 15 148 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 148 256 2 7 74 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 148 256
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 148 256 4 3 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 148 256 (accept_3_3 11 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  148 256 2 5 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 148 256 (Polychromatic418967fa.accept_24_9_4_16_1_12173 9 148 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 148 256 4 2 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 148 256 (Polychromatic418967fa.accept_21_7_1_4_1_4985 7 148 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 256 2 3 74 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 256 (accept_3_3 5
  148 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148 256 4 1 37 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 148 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 148 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 148 256 2 1 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 148 256 (Polychromatic418967fa.accept_13_1_5_9_1_226 1 148 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 148
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 147 256 (Eq.refl Bool.true) (allA_succ_of_accept 109 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  109 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 147 256
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 108 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 147 256 (accept_3_3 107 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 147 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 106 147 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 147 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 105 147
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 147 256 (accept_3_3 104 147
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 147 256
  (Polychromatic418967fa.accept_6_1_3_4_1_1 103 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 147 256 (Polychromatic418967fa.accept_12_6_3_4_1_394 102 147 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 147 256 (accept_3_3 101 147 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 147 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 100 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 147 256
  (Polychromatic418967fa.accept_13_8_4_9_1_1145 99 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 147 256 (accept_3_3 98 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 147 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 96 147 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 147 256 (accept_3_3 95 147 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 147 256 (Polychromatic418967fa.accept_14_10_7_4_1_3453 94 147 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 147 256
  (Polychromatic418967fa.accept_10_3_7_6_1_659 93 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 147 256 (accept_3_3 92 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 147 256 (Polychromatic418967fa.accept_12_6_3_4_1_394 90 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 147 256 (accept_3_3 89 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 147 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 147 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 147 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 87 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 147 256 (accept_3_3 86 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 147 256 (Polychromatic418967fa.accept_11_7_4_3_1_302 84 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 147 256 (accept_3_3 83 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 147 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 147 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 147 256
  (Polychromatic418967fa.accept_10_1_7_6_1_91 81 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 147 256 (accept_3_3 80 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 147 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 78 147 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 147 256 (accept_3_3 77 147 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 147 256 (Polychromatic418967fa.accept_17_8_11_1_1_5761 76 147 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 147 256
  (Polychromatic418967fa.accept_17_7_11_1_1_4503 75 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 147 256 (accept_3_3 74 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 147 256 (Polychromatic418967fa.accept_13_7_4_9_1_1865 72 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 147 256 (accept_3_3 71 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 147 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 147 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 147 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 147 256 (accept_3_3 68 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 147 256 (Polychromatic418967fa.accept_12_6_3_4_1_394 66 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 147 256 (accept_3_3 65 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 147 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 147 256
  (Polychromatic418967fa.accept_10_3_7_6_1_659 63 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 147 256 (accept_3_3 62 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 147 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 147 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 256 (accept_3_3 59 147 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 256 (Polychromatic418967fa.accept_13_6_4_9_1_4326 58 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 147 256
  (Polychromatic418967fa.accept_13_5_4_9_1_601 57 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 147 256 (accept_3_3 56 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 147 256 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 256 (accept_3_3 53 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 147 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 147 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 147 256 (accept_3_3 50 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 147 256 (Polychromatic418967fa.accept_22_4_15_14_1_15611 48 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 256 (accept_3_3 47 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 147 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 256
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 45 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 147 256 (accept_3_3 44 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 147 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 147 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 256 (accept_3_3 41 147 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 256 (Polychromatic418967fa.accept_11_7_4_3_1_302 40 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 256
  (Polychromatic418967fa.accept_14_11_7_4_1_3449 39 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 147 256 (accept_3_3 38 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 147 256 (Polychromatic418967fa.accept_19_17_14_9_1_8833 36 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 256 (accept_3_3 35 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 147 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 147 256 (accept_3_3 32 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 147 256 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 256 (accept_3_3 29 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 147 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 256
  (Polychromatic418967fa.accept_17_10_11_1_1_5784 27 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 256 (accept_3_3 26 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 147 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 147 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 256 (accept_3_3 23 147 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 256
  (Polychromatic418967fa.accept_19_3_14_9_1_8866 22 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 147 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 147 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 256 (accept_3_3 20 147 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 147 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 256 (Polychromatic418967fa.accept_11_7_4_3_1_302
  18 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 256 (accept_3_3 17
  147 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 16 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 147 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 147 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 256 (accept_3_3 14 147 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 147 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 256
  (Polychromatic418967fa.accept_19_12_14_9_1_10229 12 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 147 256 (accept_3_3 11 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 147 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 256 (Polychromatic418967fa.accept_20_9_7_16_1_4030 9 147
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 256 (accept_3_3 8 147 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 147 256 (accept_3_3 5 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  147 256 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 147 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 147 256 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 147 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 256 (accept_3_3 2 147 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 147 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 111 146 256 (Eq.refl Bool.true) (allA_of_3_1 111 146 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 112 145 256 (Eq.refl Bool.true) (allA_succ_of_accept 111 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 145 256 (accept_3_3 110 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 145 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 109 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 145 256 (Polychromatic418967fa.accept_23_16_7_3_1_10710 108 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 145 256 (accept_3_3 107 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 145 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 106 145
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 145 256 (accept_3_3 104 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 145 256 (Polychromatic418967fa.accept_15_13_10_1_1_1862 103 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 145 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 102 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 145 256 (accept_3_3 101 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 145 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 100 145
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 145 256 (accept_3_3 98 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 145 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 97 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 145 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 96 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 145 256 (accept_3_3 95 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 145 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 94 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 145 256 (accept_3_3 92 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 145 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 91 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 145 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 90 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 145 256 (accept_3_3 89 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 145 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 145 256 (accept_3_3 86 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 145 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 85 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 145 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 145 256 (accept_3_3 83 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 145 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 82 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 145 256 (accept_3_3 80 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 145 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 79 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 145 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 145 256 (accept_3_3 77 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 145 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 145 256 (accept_3_3 74 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 145 256 (Polychromatic418967fa.accept_15_13_10_1_1_1862 73 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 145 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 145 256 (accept_3_3 71 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 145 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 145 256 (accept_3_3 68 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 145 256 (Polychromatic418967fa.accept_11_1_2_3_1_688 67 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 145 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 145 256 (accept_3_3 65 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 145 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 145 256 (accept_3_3 62 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 145 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 145 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 145 256 (accept_3_3 59 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 145 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 145 256 (accept_3_3 56 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 145 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 145 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 145 256 (accept_3_3 53 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 145 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 145 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 145 256 (accept_3_3 50 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 145 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 49 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 145 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 256 (accept_3_3 47 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 145 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 145 256 (accept_3_3 44 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 145 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 145 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 256 (accept_3_3 41 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 145 256 (Polychromatic418967fa.accept_13_1_2_9_1_1186 40 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 145 256 (accept_3_3 38 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 145 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 145 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 256 (accept_3_3 35 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 145 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 145 256 (accept_3_3 32 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 145 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 145 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 256 (accept_3_3 29 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 256 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 145 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 256 (accept_3_3 26 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 145 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 145 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 256 (accept_3_3 23 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 256 (accept_3_3 20 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 256 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 256 (accept_3_3 17 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 145 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 256 (accept_3_3 14 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 256 (accept_3_3 11 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 256 (accept_3_3 8 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 256 (accept_3_3 5 145 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 145 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 256 (accept_3_3 2 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 145 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 144 256 (Eq.refl Bool.true) (allA_succ_of_gcd 112 144 256 16 7 9 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 144 256
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 111 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 144 256 2 55 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 144 256 (Polychromatic418967fa.accept_13_5_1_9_1_618 109 144 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 144 256 4 27 36 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 144 256 (accept_3_3 107 144 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 144 256 2 53 72 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 144 256
  (Polychromatic418967fa.accept_10_5_4_6_1_319 105 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 144 256 8 13 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 144 256 (Polychromatic418967fa.accept_19_8_11_9_1_8827 103 144 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 144 256 2 51 72 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 144 256 (accept_3_3 101 144 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 144 256 4 25 36 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 144 256
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 99 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 144 256 2 49 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 144 256 (Polychromatic418967fa.accept_13_6_1_9_1_619 97 144 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 144 256 16 6 9 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 144 256 (accept_3_3 95 144 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 144 256 2 47 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 144 256 (Polychromatic418967fa.accept_13_2_1_9_1_1174
  93 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 144 256 4 23 36 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 144 256
  (Polychromatic418967fa.accept_19_15_11_9_1_11629 91 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 144 256 2 45 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 144 256 (accept_3_3 89 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 144 256 8 11 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 144 256 (Polychromatic418967fa.accept_21_3_18_4_1_11234 87 144 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 144 256 2 43 72 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 144 256
  (Polychromatic418967fa.accept_10_5_4_6_1_319 85 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 144 256 4 21 36 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 144 256 (accept_3_3 83 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 144 256 2 41 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 144 256 (Polychromatic418967fa.accept_15_6_9_1_1_1823 81 144 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 144 256 16 5 9 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 144 256
  (Polychromatic418967fa.accept_11_2_1_3_1_683 79 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 144 256 2 39 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 144 256 (accept_3_3 77 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 144 256 4 19 36 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 144 256 (Polychromatic418967fa.accept_10_5_4_6_1_319 75 144 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 144 256 2 37 72 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 144 256
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 73 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 144 256 8 9 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 144 256 (accept_3_3 71 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  144 256 2 35 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 144 256 (Polychromatic418967fa.accept_21_6_18_4_1_4952 69 144 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 144 256 4 17 36 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 144 256 (Polychromatic418967fa.accept_13_2_1_9_1_1174
  67 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 144 256 2 33 72 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 144 256
  (accept_3_3 65 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 144 256 16 4 9 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 144 256
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 63 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 144 256 2 31 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 144 256 (Polychromatic418967fa.accept_21_19_18_4_1_4977 61 144 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 144 256 4 15 36 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 144 256 (accept_3_3 59 144 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 256 2 29 72 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 144 256
  (Polychromatic418967fa.accept_11_2_1_3_1_683 57 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 144 256 8 7 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 144 256 (Polychromatic418967fa.accept_10_5_4_6_1_319 55 144 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 144 256 2 27 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 144 256 (accept_3_3 53 144 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 256 4 13 36 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 144 256 (Polychromatic418967fa.accept_15_6_9_1_1_1823 51 144
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 144 256 2 25 72 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 256
  (Polychromatic418967fa.accept_13_10_1_9_1_3380 49 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 256 16 3 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 144 256 (accept_3_3 47 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  144 256 2 23 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 144 256 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 144 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 144 256 4 11 36 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 256 (Polychromatic418967fa.accept_17_9_8_1_1_7036
  43 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 144 256 2 21 72 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 144 256
  (accept_3_3 41 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 256 8 5 18 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 144 256
  (Polychromatic418967fa.accept_19_1_11_9_1_10307 39 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 144 256 2 19 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 144 256 (Polychromatic418967fa.accept_13_11_1_9_1_1179 37 144 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 144 256 4 9 36 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 144 256 (accept_3_3 35 144 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 256 2 17 72 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 144 256
  (Polychromatic418967fa.accept_19_14_11_9_1_3330 33 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 144 256 16 2 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 144 256 (Polychromatic418967fa.accept_13_5_1_9_1_618 31 144 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 144 256 2 15 72 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 144 256 (accept_3_3 29 144 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 256 4 7 36 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 256
  (Polychromatic418967fa.accept_19_8_11_9_1_8827 27 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 144 256 2 13 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 144 256 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 144 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 144 256 8 3 18 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 144 256 (accept_3_3 23 144 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 256 2 11 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 256 (Polychromatic418967fa.accept_13_8_1_9_1_1178
  21 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 144 256 4 5 36 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 256
  (Polychromatic418967fa.accept_13_6_1_9_1_619 19 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 256 2 9 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 144 256 (accept_3_3 17 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 144 256 16 1 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 144 256 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 144 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 256 2 7 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 256 (Polychromatic418967fa.accept_11_2_1_3_1_683
  13 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 256 4 3 36 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 256
  (accept_3_3 11 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 256 2 5 72 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 144 256
  (Polychromatic418967fa.accept_17_9_8_1_1_7036 9 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 144 256 8 1 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 256 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 144 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 256 2 3 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 256 (accept_3_3 5 144 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 256 4 1 36 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 144 256 (Polychromatic418967fa.accept_19_3_11_9_1_10217 3 144 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 256 2 1 72 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 256
  (Polychromatic418967fa.accept_19_1_11_9_1_10307 1 144 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 144
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 114 143 256 (Eq.refl Bool.true) (allA_of_3_1 114 143 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 115 142 256 (Eq.refl Bool.true) (allA_succ_of_gcd 114 142 256 2 57 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 142 256 (accept_3_3 113 142 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 142 256 2 56 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 142 256 (Polychromatic418967fa.accept_7_6_2_4_1_291
  111 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 142 256 2 55 71 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 142 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 109 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 142 256 2 54 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 142 256 (accept_3_3 107 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 142 256 2 53 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 142 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 105 142 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 142 256 2 52 71 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 142 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 103 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 142 256 2 51 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 142 256 (accept_3_3 101 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 142 256 2 50 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 142 256 (Polychromatic418967fa.accept_13_8_12_9_1_1168 99 142 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 142 256 2 49 71 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 142 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 97 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 142 256 2 48 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 142 256 (accept_3_3 95 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 142 256 2 47 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 142 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 93 142 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 142 256 2 46 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 142 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 91 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 142 256 2 45 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 142 256 (accept_3_3 89 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 142 256 2 44 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 142 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 87 142 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 142 256 2 43 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 142 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 85 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 142 256 2 42 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 142 256 (accept_3_3 83 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 142 256 2 41 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 142 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 142 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 142 256 2 40 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 142 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 79 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 142 256 2 39 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 142 256 (accept_3_3 77 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 142 256 2 38 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 142 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 142 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 142 256 2 37 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 142 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 73 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 142 256 2 36 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 142 256 (accept_3_3 71 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 142 256 2 35 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 142 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 142 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 142 256 2 34 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 142 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 142 256 2 33 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 142 256 (accept_3_3 65 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 142 256 2 32 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 142 256 (Polychromatic418967fa.accept_17_12_6_1_1_4517 63 142 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 142 256 2 31 71 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 142 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 61 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 142 256 2 30 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 142 256 (accept_3_3 59 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 142 256 2 29 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 142 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 142 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 142 256 2 28 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 142 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 142 256 2 27 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 142 256 (accept_3_3 53 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 142 256 2 26 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 142 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 142 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 142 256 2 25 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 142 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 142 256 2 24 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 142 256 (accept_3_3 47 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 142 256 2 23 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 142 256 (Polychromatic418967fa.accept_22_1_10_14_1_10991 45 142 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 142 256 2 22 71 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 142 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 142 256 2 21 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 142 256 (accept_3_3 41 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 142 256 2 20 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 142 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 142 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 142 256 2 19 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 37 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 142 256 2 18 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 142 256 (accept_3_3 35 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 256 2 17 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 142 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 256 2 16 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 256
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 256 2 15 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 256 (accept_3_3 29 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 256 2 14 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 142 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 256 2 13 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 256 2 12 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 256 (accept_3_3 23 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 256 2 11 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 142 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 256 2 10 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 256 2 9 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 142 256 (accept_3_3 17 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 142 256 2 8 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 142 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 142 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 142 256 2 7 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 142 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 142 256 2 6 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 142 256 (accept_3_3 11 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 142 256 2 5 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 142 256 (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 142 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 142 256 2 4 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 142 256
  (Polychromatic418967fa.accept_11_7_10_3_1_633 7 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 142 256 2 3 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 142 256 (accept_3_3 5 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 142
  256 2 2 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  142 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 142 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 142 256 2 1 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 142 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 142 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 141 256 (Eq.refl Bool.true) (allA_succ_of_accept 115 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  115 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 141 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 114 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 141 256 (accept_3_3 113 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 141 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 112 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 141 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 111 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 141 256 (accept_3_3 110 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 141 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 141 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 108 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 141 256 (accept_3_3 107 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 141 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 106 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 141 256 (Polychromatic418967fa.accept_10_5_1_6_1_672 105 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 141 256 (accept_3_3 104 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 141 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 141 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 102 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 141 256 (accept_3_3 101 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 141 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 100 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 141 256 (Polychromatic418967fa.accept_13_8_11_9_1_593 99 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 141 256 (accept_3_3 98 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 141 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 141 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 96 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 141 256 (accept_3_3 95 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 141 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 94 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 141 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 93 141 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 141 256 (accept_3_3 92 141 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 141 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 90 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 141 256 (accept_3_3 89 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 141 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 88 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 141 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 141 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 141 256 (accept_3_3 86 141 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 141 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 141 256 (accept_3_3 83 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 141 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 82 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 141 256 (Polychromatic418967fa.accept_14_11_1_4_1_4445 81 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 141 256 (accept_3_3 80 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 141 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 141 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 78 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 141 256 (accept_3_3 77 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 141 256 (Polychromatic418967fa.accept_24_4_21_16_1_12146 76 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 141 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 141 256 (accept_3_3 74 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 141 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 256
  (Polychromatic418967fa.accept_10_2_1_6_1_634 72 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 141 256 (accept_3_3 71 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 141 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 141 256 (Polychromatic418967fa.accept_15_9_6_1_1_493 69 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 256 (accept_3_3 68 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 141 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 66 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 141 256 (accept_3_3 65 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 141 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 141 256 (Polychromatic418967fa.accept_15_3_6_1_1_1834 63 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 256 (accept_3_3 62 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 141 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 256
  (Polychromatic418967fa.accept_13_8_11_9_1_593 60 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 141 256 (accept_3_3 59 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 141 256 (Polychromatic418967fa.accept_19_1_8_9_1_3304 58 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 141 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 141 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 256 (accept_3_3 56 141 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 141 256 (accept_3_3 53 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 141 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 141 256 (Polychromatic418967fa.accept_20_11_1_16_1_8513 51 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 256 (accept_3_3 50 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 141 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 141 256 (accept_3_3 47 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 141 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 141 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 141 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 256 (accept_3_3 44 141 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 256
  (Polychromatic418967fa.accept_10_2_1_6_1_634 42 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 141 256 (accept_3_3 41 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 141 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 141 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 141 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 256 (accept_3_3 38 141 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 256
  (Polychromatic418967fa.accept_19_17_8_9_1_10148 36 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 141 256 (accept_3_3 35 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 141 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 141 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 256 (accept_3_3 32 141 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 141 256 (accept_3_3 29 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 141 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 141 256 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 256 (accept_3_3 26 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 141 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 141 256 (accept_3_3 23 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 141 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 141 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 141 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 256 (accept_3_3 20 141 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 256
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 141 256 (accept_3_3 17 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 141 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 141 256 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 256 (accept_3_3 14 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 141 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 141 256 (accept_3_3 11 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 141 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 141 256 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 141 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 256 (accept_3_3 8 141 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 256
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 141 256 (accept_3_3 5 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  141 256 (Polychromatic418967fa.accept_17_4_5_1_1_5776 4 141 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 141 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 141 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 256 (accept_3_3 2 141 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 141 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 117 140 256 (Eq.refl Bool.true) (allA_of_3_1 117 140 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 118 139 256 (Eq.refl Bool.true) (allA_succ_of_accept 117 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 117 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 139 256 (accept_3_3 116 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 139 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 115 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 139 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 114 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 139 256 (accept_3_3 113 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 139 256 (Polychromatic418967fa.accept_19_17_6_9_1_8856 112
  139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 139 256 (accept_3_3 110 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 139 256 (Polychromatic418967fa.accept_11_10_7_3_1_3679 109 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 139 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 108 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 139 256 (accept_3_3 107 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 139 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 106 139
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 139 256 (accept_3_3 104 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 139 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 103 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 139 256 (Polychromatic418967fa.accept_15_12_4_1_1_3746 102 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 139 256 (accept_3_3 101 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 139 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 100 139
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 139 256 (accept_3_3 98 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 139 256 (Polychromatic418967fa.accept_18_7_13_4_1_1670 97 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 139 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 96 139 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 139 256 (accept_3_3 95 139 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 139 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 94 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 139 256 (accept_3_3 92 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 139 256 (Polychromatic418967fa.accept_17_6_3_1_1_7011 91 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 139 256 (Polychromatic418967fa.accept_19_14_6_9_1_5990 90 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 139 256 (accept_3_3 89 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 139 256 (Polychromatic418967fa.accept_26_10_9_22_1_15640 88
  139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 139 256 (accept_3_3 86 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 139 256 (Polychromatic418967fa.accept_10_5_9_6_1_697 85 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 139 256 (Polychromatic418967fa.accept_22_18_7_14_1_11033 84 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 139 256 (accept_3_3 83 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 139 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 82 139 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 139 256 (accept_3_3 80 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 139 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 79 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 139 256 (Polychromatic418967fa.accept_15_3_4_1_1_1072 78 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 139 256 (accept_3_3 77 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 139 256 (Polychromatic418967fa.accept_11_10_7_3_1_3679 76 139
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 139 256 (accept_3_3 74 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 139 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 139 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 139 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 139 256 (accept_3_3 71 139 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 139 256 (Polychromatic418967fa.accept_11_4_7_3_1_289 70 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 139 256 (accept_3_3 68 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 139 256 (Polychromatic418967fa.accept_19_10_6_9_1_7312 67 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 139 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 139 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 139 256 (accept_3_3 65 139 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 139 256 (Polychromatic418967fa.accept_18_10_13_4_1_5153 64 139 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 139 256 (accept_3_3 62 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 139 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 139 256 (Polychromatic418967fa.accept_17_9_3_1_1_2275 60 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 139 256 (accept_3_3 59 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 139 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 139 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 139 256 (accept_3_3 56 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 139 256 (Polychromatic418967fa.accept_10_5_9_6_1_697 55 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 139 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 139 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 139 256 (accept_3_3 53 139 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 139 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 139 256 (accept_3_3 50 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 139 256 (Polychromatic418967fa.accept_17_15_3_1_1_9696 49 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 139 256 (Polychromatic418967fa.accept_11_4_7_3_1_289 48 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 256 (accept_3_3 47 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 139
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 256 (accept_3_3 44 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 43 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 256 (Polychromatic418967fa.accept_15_12_4_1_1_3746 42 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 256 (accept_3_3 41 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 139 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 256 (accept_3_3 38 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 256 (Polychromatic418967fa.accept_17_2_3_1_1_2244 36 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 256 (accept_3_3 35 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 139
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 256 (accept_3_3 32 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 139 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 256 (accept_3_3 29 139 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 256 (Polychromatic418967fa.accept_18_10_13_4_1_5153 28 139 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 256 (accept_3_3 26 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 256 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 139 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 256 (accept_3_3 23 139 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 256 (accept_3_3 20 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 256 (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 256 (accept_3_3 17 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 139 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 256 (accept_3_3 14 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 139 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 256 (accept_3_3 11 139 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 256 (accept_3_3 8 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 256 (Polychromatic418967fa.accept_18_7_13_4_1_1670 7 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 256 (Polychromatic418967fa.accept_17_6_3_1_1_7011 6 139 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 256 (accept_3_3 5 139 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 256 (Polychromatic418967fa.accept_11_4_7_3_1_289 4 139 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 256 (accept_3_3 2 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 256 (Polychromatic418967fa.accept_21_1_13_4_1_11180 1 139 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 138 256 (Eq.refl Bool.true) (allA_succ_of_gcd 118 138 256 2 59 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 138 256
  (Polychromatic418967fa.accept_12_9_6_4_1_402 117 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 138 256 2 58 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 138 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 115 138 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 138 256 2 57 69 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 138 256 (accept_3_3 113 138 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 138 256 2 56 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 138 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 111 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 138 256 2 55 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 138 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 109 138 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 138 256 2 54 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 138 256 (accept_3_3 107 138 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 138 256 2 53 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 138 256 (Polychromatic418967fa.accept_9_6_3_4_1_477
  105 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 138 256 2 52 69 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 138 256
  (Polychromatic418967fa.accept_10_3_8_6_1_326 103 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 138 256 2 51 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 138 256 (accept_3_3 101 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 138 256 2 50 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 138 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 99 138 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 138 256 2 49 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 138 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 97 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 138 256 2 48 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 138 256 (accept_3_3 95 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 138 256 2 47 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 138 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 93 138 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 138 256 2 46 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 138 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 91 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 138 256 2 45 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 138 256 (accept_3_3 89 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 138 256 2 44 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 138 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 87 138 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 138 256 2 43 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 138 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 85 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 138 256 2 42 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 138 256 (accept_3_3 83 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 138 256 2 41 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 138 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 81 138 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 138 256 2 40 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 138 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 79 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 138 256 2 39 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 138 256 (accept_3_3 77 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 138 256 2 38 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 138 256 (Polychromatic418967fa.accept_11_9_6_3_1_1668 75 138 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 138 256 2 37 69 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 138 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 73 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 256 2 36 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 256 (accept_3_3 71 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 138 256 2 35 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 138 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 138 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 138 256 2 34 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 138 256
  (Polychromatic418967fa.accept_17_16_2_1_1_4492 67 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 256 2 33 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 256 (accept_3_3 65 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 138 256 2 32 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 138 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 138 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 138 256 2 31 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 138 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 61 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 256 2 30 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 256 (accept_3_3 59 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 138 256 2 29 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 138 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 138 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 138 256 2 28 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 138 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 55 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 256 2 27 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 256 (accept_3_3 53 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 138 256 2 26 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 138 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 138 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 138 256 2 25 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 256
  (Polychromatic418967fa.accept_15_4_3_1_1_487 49 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 256 2 24 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 256 (accept_3_3 47 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 138 256 2 23 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 138 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 138 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 138 256 2 22 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 256 2 21 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 256 (accept_3_3 41 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 138 256 2 20 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 138 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 138 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 138 256 2 19 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 256 2 18 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 256 (accept_3_3 35 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 138 256 2 17 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 138 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 138 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 138 256 2 16 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 256
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 31 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 256 2 15 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 256 (accept_3_3 29 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 138 256 2 14 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 138 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 138 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 138 256 2 13 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 256 2 12 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 256 (accept_3_3 23 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 138 256 2 11 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 138 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 138 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 138 256 2 10 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 256 2 9 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 138 256 (accept_3_3 17 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 138 256 2 8 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 138 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 138 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 138 256 2 7 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 256 2 6 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 138 256 (accept_3_3 11 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 256 2 5 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 138 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 138 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 138 256 2 4 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 138 256 2 3 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 138 256 (accept_3_3 5 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138
  256 2 2 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  138 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 138 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 138 256 2 1 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 138 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 138 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 120 137 256 (Eq.refl Bool.true) (allA_of_3_1 120 137 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 121 136 256 (Eq.refl Bool.true) (allA_succ_of_gcd 120 136 256 8 15 17 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 136 256 (accept_3_3 119 136 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 136 256 2 59 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 136 256 (Polychromatic418967fa.accept_11_7_4_3_1_302
  117 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 136 256 4 29 34 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 136 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 115 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 136 256 2 57 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 136 256 (accept_3_3 113 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 136 256 8 14 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 136 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 111 136 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 136 256 2 55 68 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 136 256
  (Polychromatic418967fa.accept_19_14_3_9_1_2157 109 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 136 256 4 27 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 136 256 (accept_3_3 107 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 136 256 2 53 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 136 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 105 136 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 136 256 8 13 17 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 136 256
  (Polychromatic418967fa.accept_18_13_10_4_1_5150 103 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 136 256 2 51 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 136 256 (accept_3_3 101 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 136 256 4 25 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 136 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 99 136 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 136 256 2 49 68 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 136 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 97 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 136 256 8 12 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 136 256 (accept_3_3 95 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 136 256 2 47 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 136 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 93 136 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 136 256 4 23 34 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 136 256
  (Polychromatic418967fa.accept_14_7_10_4_1_130 91 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 136 256 2 45 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 136 256 (accept_3_3 89 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 136 256 8 11 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 136 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 87 136 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 136 256 2 43 68 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 136 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 85 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 136 256 4 21 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 136 256 (accept_3_3 83 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 136 256 2 41 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 136 256 (Polychromatic418967fa.accept_13_3_6_9_1_1150 81 136 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 136 256 8 10 17 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 136 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 79 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 136 256 2 39 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 136 256 (accept_3_3 77 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 136 256 4 19 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 136 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 75 136 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 136 256 2 37 68 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 136 256
  (Polychromatic418967fa.accept_11_7_4_3_1_302 73 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 136 256 8 9 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 136 256 (accept_3_3 71 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  136 256 2 35 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 136 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 136 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 136 256 4 17 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 136 256 (Polychromatic418967fa.accept_13_2_6_9_1_2636
  67 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 136 256 2 33 68 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 136 256
  (accept_3_3 65 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 136 256 8 8 17 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 136 256
  (Polychromatic418967fa.accept_14_7_10_4_1_130 63 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 136 256 2 31 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 136 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 136 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 136 256 4 15 34 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 136 256 (accept_3_3 59 136 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 136 256 2 29 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 136 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 57
  136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 136 256 8 7 17 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 136 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 55 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 136 256 2 27 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 136 256 (accept_3_3 53 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 136 256 4 13 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 136 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 136 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 136 256 2 25 68 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 136 256
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 49 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 136 256 8 6 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 136 256 (accept_3_3 47 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  136 256 2 23 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 136 256 (Polychromatic418967fa.accept_25_20_11_6_1_15639 45 136 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 136 256 4 11 34 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 136 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 136 256 2 21 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 136 256 (accept_3_3 41 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 136 256 8 5 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 136 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 136 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 136 256 2 19 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 136 256 (Polychromatic418967fa.accept_19_18_3_9_1_3333
  37 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 136 256 4 9 34 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 136 256
  (accept_3_3 35 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 136 256 2 17 68 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 136 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 136 256 8 4 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 136 256 (Polychromatic418967fa.accept_18_13_10_4_1_5150 31 136 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 136 256 2 15 68 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 136 256 (accept_3_3 29 136 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 136 256 4 7 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 136 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 27
  136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 136 256 2 13 68 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 136 256 8 3 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 136 256 (accept_3_3 23 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  136 256 2 11 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 136 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 136 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 256 4 5 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 256
  (Polychromatic418967fa.accept_21_19_10_4_1_14102 19 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 136 256 2 9 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 136 256 (accept_3_3 17 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 136 256 8 2 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 136 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 136 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 136 256 2 7 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 136 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 13
  136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 136 256 4 3 34 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 136 256 (accept_3_3 11
  136 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 136 256 2 5 68 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 136 256
  (Polychromatic418967fa.accept_26_9_6_22_1_10025 9 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 136 256 8 1 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 136 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 136 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 256 2 3 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 256 (accept_3_3 5 136 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136 256 4 1 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 136 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 136 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 136 256 2 1 68 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 136 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 136 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 136
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 122 135 256 (Eq.refl Bool.true) (allA_succ_of_accept 121 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  121 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 135 256
  (Polychromatic418967fa.accept_13_3_5_9_1_5285 120 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 135 256 (accept_3_3 119 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 135 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 118 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 135 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 117 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 135 256 (accept_3_3 116 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 115 135 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 135 256
  (Polychromatic418967fa.accept_10_4_5_6_1_651 114 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 135 256 (accept_3_3 113 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 135 256 (Polychromatic418967fa.accept_19_17_2_9_1_4582 112 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 135 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 111 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 135 256 (accept_3_3 110 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 135 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 135 256
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 108 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 135 256 (accept_3_3 107 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 135 256 (Polychromatic418967fa.accept_13_2_5_9_1_610 106 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 135 256 (Polychromatic418967fa.accept_13_1_5_9_1_226 105 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 135 256 (accept_3_3 104 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 135 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 135 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 102 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 135 256 (accept_3_3 101 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 135 256 (Polychromatic418967fa.accept_14_2_9_4_1_1735 100 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 135 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 99 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 135 256 (accept_3_3 98 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 135 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 135 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 96 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 135 256 (accept_3_3 95 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 135 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 94 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 135 256 (Polychromatic418967fa.accept_13_2_5_9_1_610 93 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 135 256 (accept_3_3 92 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 135 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 135 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 90 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 135 256 (accept_3_3 89 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 135 256 (Polychromatic418967fa.accept_19_12_2_9_1_15638 88 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 135 256 (Polychromatic418967fa.accept_17_2_16_1_1_2260 87 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 135 256 (accept_3_3 86 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 135 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 135 256
  (Polychromatic418967fa.accept_10_4_5_6_1_651 84 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 135 256 (accept_3_3 83 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 135 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 82 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 135 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 81 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 135 256 (accept_3_3 80 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 135 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 135 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 78 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 135 256 (accept_3_3 77 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 135 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 135 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 135 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 135 256 (accept_3_3 74 135 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 135 256
  (Polychromatic418967fa.accept_14_2_9_4_1_1735 72 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 135 256 (accept_3_3 71 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 135 256 (Polychromatic418967fa.accept_17_2_16_1_1_2260 70 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 135 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 135 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 256 (accept_3_3 68 135 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 135 256 (accept_3_3 65 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 135 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 64 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 135 256 (Polychromatic418967fa.accept_17_12_16_1_1_8363 63 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 256 (accept_3_3 62 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 135 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 256
  (Polychromatic418967fa.accept_21_18_9_4_1_4964 60 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 135 256 (accept_3_3 59 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 135 256 (Polychromatic418967fa.accept_14_2_9_4_1_1735 58 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 135 256 (Polychromatic418967fa.accept_21_15_9_4_1_2207 57 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 256 (accept_3_3 56 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 135 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 135 256 (accept_3_3 53 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 135 256 (Polychromatic418967fa.accept_23_6_20_3_1_15637 52 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 135 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 51 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 135 256 (accept_3_3 50 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 135 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 135 256 (accept_3_3 47 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 135 256 (Polychromatic418967fa.accept_17_12_16_1_1_8363 46 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 135 256 (Polychromatic418967fa.accept_19_7_2_9_1_6006 45 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 256 (accept_3_3 44 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 135 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 135 256 (accept_3_3 41 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 135 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 135 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 39 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 256 (accept_3_3 38 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 135 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 256
  (Polychromatic418967fa.accept_17_2_16_1_1_2260 36 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 135 256 (accept_3_3 35 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 135 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 135 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 135 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 256 (accept_3_3 32 135 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 135 256 (accept_3_3 29 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 135 256 (Polychromatic418967fa.accept_13_2_5_9_1_610 28 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 135 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 135 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 256 (accept_3_3 26 135 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 256
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 135 256 (accept_3_3 23 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 135 256 (Polychromatic418967fa.accept_17_5_16_1_1_3358 22 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 135 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 256 (accept_3_3 20 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 135 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 135 256 (accept_3_3 17 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 135 256 (Polychromatic418967fa.accept_13_3_5_9_1_5285 16 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 135 256 (Polychromatic418967fa.accept_13_2_5_9_1_610 15 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 256 (accept_3_3 14 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 135 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 135 256 (accept_3_3 11 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 135 256 (Polychromatic418967fa.accept_20_10_15_16_1_6994 10 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 256 (accept_3_3 8 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 135 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 135 256 (accept_3_3 5 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  135 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 135 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 135 256 (Polychromatic418967fa.accept_13_3_5_9_1_5285 3 135 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 256 (accept_3_3 2 135 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 135 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 123 134 256 (Eq.refl Bool.true) (allA_of_3_1 123 134 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 124 133 256 (Eq.refl Bool.true) (allA_succ_of_accept 123 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 123 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 133 256 (accept_3_3 122 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 133 256 (Polychromatic418967fa.accept_18_13_7_4_1_2738 121 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 120 133 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 120 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 133 256 (accept_3_3 119 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 133 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 118 133
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 117 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 133 256 (accept_3_3 116 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 133 256 (Polychromatic418967fa.accept_14_3_7_4_1_118 115 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 133 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 114 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 133 256 (accept_3_3 113 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 133 256 (Polychromatic418967fa.accept_11_2_1_3_1_683 112 133
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 133 256 (accept_3_3 110 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 133 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 109 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 133 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 108 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 133 256 (accept_3_3 107 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 133 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 106 133
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 133 256 (accept_3_3 104 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 133 256 (Polychromatic418967fa.accept_13_12_3_9_1_4341 103 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 133 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 102 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 133 256 (accept_3_3 101 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 133 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 100 133
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 133 256 (accept_3_3 98 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 133 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 97 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 133 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 96 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 133 256 (accept_3_3 95 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 133 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 94 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 133 256 (accept_3_3 92 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 133 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 133 256 (Polychromatic418967fa.accept_11_2_1_3_1_683 90 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 133 256 (accept_3_3 89 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 133 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 88 133
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 133 256 (accept_3_3 86 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 133 256 (Polychromatic418967fa.accept_13_7_3_9_1_1142 85 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 133 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 133 256 (accept_3_3 83 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 133 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 133 256 (accept_3_3 80 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 133 256 (Polychromatic418967fa.accept_10_9_3_6_1_686 79 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 133 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 78 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 133 256 (accept_3_3 77 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 133 256 (Polychromatic418967fa.accept_21_13_7_4_1_4991 76 133 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 133 256 (accept_3_3 74 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 133 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 133 256 (Polychromatic418967fa.accept_13_7_3_9_1_1142 72 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 133 256 (accept_3_3 71 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 133 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 133
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 133 256 (accept_3_3 68 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 133 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 67 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 133 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 256 (accept_3_3 65 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 133 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 133 256 (accept_3_3 62 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 133 256 (Polychromatic418967fa.accept_17_10_14_1_1_5823 61 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 133 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 256 (accept_3_3 59 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 133 256 (accept_3_3 56 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 133 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 133 256 (Polychromatic418967fa.accept_13_2_3_9_1_2610 54 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 133 256 (accept_3_3 53 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 133 256 (Polychromatic418967fa.accept_14_10_7_4_1_3453 52 133
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 133 256 (accept_3_3 50 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 133 256 (Polychromatic418967fa.accept_10_9_3_6_1_686 49 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 133 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 256 (accept_3_3 47 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 133 256 (accept_3_3 44 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 133 256 (Polychromatic418967fa.accept_20_3_13_16_1_641 43 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 133 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 256 (accept_3_3 41 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 256 (Polychromatic418967fa.accept_15_10_13_1_1_3698 40 133 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 256 (accept_3_3 38 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 256 (Polychromatic418967fa.accept_24_12_13_16_1_5138 36 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 256 (accept_3_3 35 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 133
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 256 (accept_3_3 32 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 256 (Polychromatic418967fa.accept_13_5_3_9_1_1189 31 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 256 (accept_3_3 29 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 256 (accept_3_3 26 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 256 (Polychromatic418967fa.accept_13_12_3_9_1_4341 25 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 256 (accept_3_3 23 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 256 (accept_3_3 20 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 256 (accept_3_3 17 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 256 (Polychromatic418967fa.accept_18_16_7_4_1_3901 16 133
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 256 (accept_3_3 14 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 256 (Polychromatic418967fa.accept_11_2_1_3_1_683 13 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 256 (accept_3_3 11 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 256 (accept_3_3 8 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 256 (accept_3_3 5 133 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 256 (Polychromatic418967fa.accept_17_4_14_1_1_1363 4 133 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 256 (accept_3_3 2 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 133 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 125 132 256 (Eq.refl Bool.true) (allA_succ_of_gcd 124 132 256 4 31 33 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 132 256
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 123 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 132 256 2 61 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 132 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 121 132 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 132 256 4 30 33 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 132 256 (accept_3_3 119 132 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 132 256 2 59 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 132 256 (Polychromatic418967fa.accept_7_5_6_4_1_117
  117 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 132 256 4 29 33 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 132 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 115 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 132 256 2 57 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 132 256 (accept_3_3 113 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 132 256 4 28 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 132 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 111 132 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 132 256 2 55 66 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 132 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 109 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 132 256 4 27 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 132 256 (accept_3_3 107 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 132 256 2 53 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 132 256 (Polychromatic418967fa.accept_13_1_2_9_1_1186 105 132 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 132 256 4 26 33 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 132 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 103 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 132 256 2 51 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 132 256 (accept_3_3 101 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 132 256 4 25 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 132 256 (Polychromatic418967fa.accept_17_14_13_1_1_3356 99 132 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 132 256 2 49 66 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 132 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 97 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 132 256 4 24 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 132 256 (accept_3_3 95 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 132 256 2 47 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 132 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 93 132 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 132 256 4 23 33 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 132 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 91 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 132 256 2 45 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 132 256 (accept_3_3 89 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 132 256 4 22 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 132 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 132 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 132 256 2 43 66 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 132 256
  (Polychromatic418967fa.accept_13_7_2_9_1_1826 85 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 132 256 4 21 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 132 256 (accept_3_3 83 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 132 256 2 41 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 132 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 132 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 132 256 4 20 33 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 132 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 79 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 256 2 39 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 256 (accept_3_3 77 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 132 256 4 19 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 132 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 132 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 132 256 2 37 66 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 132 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 73 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 256 4 18 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 256 (accept_3_3 71 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 132 256 2 35 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 132 256 (Polychromatic418967fa.accept_18_15_6_4_1_5147 69 132 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 132 256 4 17 33 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 132 256
  (Polychromatic418967fa.accept_19_10_18_9_1_11636 67 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 132 256 2 33 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 132 256 (accept_3_3 65 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 132 256 4 16 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 132 256 (Polychromatic418967fa.accept_13_11_2_9_1_2640 63 132 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 132 256 2 31 66 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 132 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 61 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 256 4 15 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 256 (accept_3_3 59 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 132 256 2 29 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 132 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 132 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 132 256 4 14 33 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 132 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 55 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 256 2 27 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 256 (accept_3_3 53 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 132 256 4 13 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 132 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 132 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 132 256 2 25 66 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 132 256
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 49 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 256 4 12 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 256 (accept_3_3 47 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 132 256 2 23 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 132 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 132 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 132 256 4 11 33 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 256 2 21 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 256 (accept_3_3 41 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 132 256 4 10 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 132 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 132 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 132 256 2 19 66 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 256 4 9 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 132 256 (accept_3_3 35 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  132 256 2 17 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 132 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 132 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 132 256 4 8 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 31
  132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 256 2 15 66 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 256 (accept_3_3 29
  132 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 256 4 7 33 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 132 256
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 132 256 2 13 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 132 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 132 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 256 4 6 33 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 256 (accept_3_3 23 132 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 256 2 11 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21
  132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 132 256 4 5 33 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 256 2 9 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 132 256 (accept_3_3 17 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 132 256 4 4 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 132 256 (Polychromatic418967fa.accept_18_15_6_4_1_5147 15 132 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 132 256 2 7 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 256
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 132 256 4 3 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 132 256 (accept_3_3 11 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 132 256 2 5 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 132 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 132 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 132 256 4 2 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 7
  132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 256 2 3 66 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 256 (accept_3_3 5
  132 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 256 4 1 33 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 132 256
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 132 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 132 256 2 1 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 132 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 132 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 132
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 126 131 256 (Eq.refl Bool.true) (allA_of_3_1 126 131 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 127 130 256 (Eq.refl Bool.true) (allA_succ_of_gcd 126 130 256 2 63 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 130 256 (accept_3_3 125 130 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 130 256 2 62 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 130 256
  (Polychromatic418967fa.accept_24_3_10_16_1_6997 123 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 122 130 256 2 61 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 121 130 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 121 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 130 256 2 60 65 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 130 256 (accept_3_3
  119 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 130 256 2 59 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 130 256
  (Polychromatic418967fa.accept_22_7_20_14_1_14040 117 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 130 256 2 58 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 130 256 (Polychromatic418967fa.accept_12_7_10_4_1_382 115 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 130 256 2 57 65 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 130 256 (accept_3_3
  113 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 130 256 2 56 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 130 256
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 111 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 110 130 256 2 55 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 130 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 109 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 130 256 2 54 65 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 130 256 (accept_3_3
  107 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 130 256 2 53 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 130 256
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 105 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 130 256 2 52 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 130 256 (Polychromatic418967fa.accept_12_7_10_4_1_382 103 130 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 130 256 2 51 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 130 256 (accept_3_3 101 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 130 256 2 50 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 130 256
  (Polychromatic418967fa.accept_15_9_10_1_1_1062 99 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 130 256 2 49 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 130 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 97 130 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 130 256 2 48 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 130 256 (accept_3_3 95 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 130 256 2 47 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 130 256
  (Polychromatic418967fa.accept_17_8_11_1_1_5761 93 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 130 256 2 46 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 130 256 (Polychromatic418967fa.accept_12_7_10_4_1_382 91 130 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 130 256 2 45 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 130 256 (accept_3_3 89 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 130 256 2 44 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 130 256
  (Polychromatic418967fa.accept_23_18_15_3_1_15636 87 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 130 256 2 43 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 130 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 85 130 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 130 256 2 42 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 130 256 (accept_3_3 83 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 130 256 2 41 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 130 256
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 81 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 130 256 2 40 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 130 256 (Polychromatic418967fa.accept_12_7_10_4_1_382 79 130 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 130 256 2 39 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 130 256 (accept_3_3 77 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 130 256 2 38 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 130 256
  (Polychromatic418967fa.accept_17_7_11_1_1_4503 75 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 130 256 2 37 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 130 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 73 130 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 130 256 2 36 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 130 256 (accept_3_3 71 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 130 256 2 35 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 130 256
  (Polychromatic418967fa.accept_15_9_10_1_1_1062 69 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 130 256 2 34 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 130 256 (Polychromatic418967fa.accept_12_7_10_4_1_382 67 130 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 130 256 2 33 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 130 256 (accept_3_3 65 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 130 256 2 32 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 130 256
  (Polychromatic418967fa.accept_19_6_16_9_1_10184 63 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 130 256 2 31 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 130 256 (Polychromatic418967fa.accept_11_6_9_3_1_1103 61 130 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 130 256 2 30 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 130 256 (accept_3_3 59 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 130 256 2 29 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 130 256
  (Polychromatic418967fa.accept_23_11_15_3_1_13917 57 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 130 256 2 28 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 130 256 (Polychromatic418967fa.accept_12_7_10_4_1_382 55 130 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 130 256 2 27 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 130 256 (accept_3_3 53 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 130 256 2 26 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 130 256
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 51 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 130 256 2 25 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 130 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 49 130 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 130 256 2 24 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 130 256 (accept_3_3 47 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 130 256 2 23 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 130 256
  (Polychromatic418967fa.accept_19_7_16_9_1_398 45 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 130 256 2 22 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 130 256 (Polychromatic418967fa.accept_12_7_10_4_1_382 43 130 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 130 256 2 21 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 130 256 (accept_3_3 41 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 130 256 2 20 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 130 256
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 39 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 130 256 2 19 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 130 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 130 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 130 256 2 18 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 130 256 (accept_3_3 35 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 130 256 2 17 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 130 256
  (Polychromatic418967fa.accept_19_14_16_9_1_8834 33 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 130 256 2 16 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 130 256 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 130 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 130 256 2 15 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 130 256 (accept_3_3 29 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 130 256 2 14 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 130 256
  (Polychromatic418967fa.accept_17_10_11_1_1_5784 27 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 130 256 2 13 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 130 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 130 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 130 256 2 12 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 130 256 (accept_3_3 23 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 130 256 2 11 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 130 256
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 21 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 130 256 2 10 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 130 256 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 130 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 130 256 2 9 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 130 256 (accept_3_3 17 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 130 256 2 8 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 130 256
  (Polychromatic418967fa.accept_20_15_10_16_1_8506 15 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 130 256 2 7 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 130 256 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 130 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 130 256 2 6 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 256 (accept_3_3 11 130 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 256 2 5 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 256
  (Polychromatic418967fa.accept_15_9_10_1_1_1062 9 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 130 256 2 4 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 130 256 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 130 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 256 2 3 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 130 256 (accept_3_3 5 130 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 130 256 2 2 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 130 256 (Polychromatic418967fa.accept_24_3_10_16_1_6997 3 130
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 256 2 1 65 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 130 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 130
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 128 129 256 (Eq.refl Bool.true) (allA_succ_of_accept 127 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  127 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 129 256
  (Polychromatic418967fa.accept_11_5_8_3_1_66 126 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 129 256 (accept_3_3 125 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 129 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 124 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 129 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 123 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 129 256 (accept_3_3 122 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 121 129 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 129 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 120 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 129 256 (accept_3_3 119 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 129 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 118 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 129 256 (Polychromatic418967fa.accept_19_3_15_9_1_4576 117 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 129 256 (accept_3_3 116 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 115 129 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 129 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 114 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 129 256 (accept_3_3 113 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 129 256 (Polychromatic418967fa.accept_13_8_12_9_1_1168 112 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 129 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 111 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 129 256 (accept_3_3 110 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 129 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 129 256
  (Polychromatic418967fa.accept_19_13_15_9_1_3293 108 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 129 256 (accept_3_3 107 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 129 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 106 129 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 129 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 105 129
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 129 256 (accept_3_3 104 129
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 129 256
  (Polychromatic418967fa.accept_6_1_3_4_1_1 103 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 129 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 102 129 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 129 256 (accept_3_3 101 129 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 129 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 100 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 129 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 99 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 129 256 (accept_3_3 98 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 129 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 96 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 129 256 (accept_3_3 95 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 129 256 (Polychromatic418967fa.accept_11_6_8_3_1_2236 94 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 129 256
  (Polychromatic418967fa.accept_10_3_9_6_1_94 93 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 129 256 (accept_3_3 92 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 129 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 90 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 129 256 (accept_3_3 89 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 129 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 129 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 87 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 129 256 (accept_3_3 86 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 129 256 (Polychromatic418967fa.accept_23_15_14_3_1_15635 84 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 129 256 (accept_3_3 83 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 129 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 129 256
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 81 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 129 256 (accept_3_3 80 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 129 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 129 256 (accept_3_3 77 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 129 256
  (Polychromatic418967fa.accept_10_5_9_6_1_697 75 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 129 256 (accept_3_3 74 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 129 256 (Polychromatic418967fa.accept_11_6_8_3_1_2236 72 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 129 256 (accept_3_3 71 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 129 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 129 256 (accept_3_3 68 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 129 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 66 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 256 (accept_3_3 65 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 256
  (Polychromatic418967fa.accept_10_3_9_6_1_94 63 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 129 256 (accept_3_3 62 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 129 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 256 (accept_3_3 59 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 256 (Polychromatic418967fa.accept_17_7_10_1_1_4488 58 129 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 129 256 (accept_3_3 56 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 129 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 256 (accept_3_3 53 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 129 256 (accept_3_3 50 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 129 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 256 (accept_3_3 47 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 256
  (Polychromatic418967fa.accept_10_5_9_6_1_697 45 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 129 256 (accept_3_3 44 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 129 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 256 (accept_3_3 41 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 256 (Polychromatic418967fa.accept_15_10_9_1_1_3688 40 129 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 256
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 129 256 (accept_3_3 38 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 129 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 256 (accept_3_3 35 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 129 256 (accept_3_3 32 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 129 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 256 (accept_3_3 29 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 129 256 (accept_3_3 26 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 129 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 256 (accept_3_3 23 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 256
  (Polychromatic418967fa.accept_13_8_12_9_1_1168 21 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 129 256 (accept_3_3 20 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 129 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 256 (accept_3_3 17 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 129 256 (accept_3_3 14 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 129 256 (Polychromatic418967fa.accept_21_12_3_4_1_4988 12 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 256 (accept_3_3 11 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 129 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 256
  (Polychromatic418967fa.accept_17_9_10_1_1_3345 9 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 129 256 (accept_3_3 8 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 129 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 256 (accept_3_3 5 129 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 256 (Polychromatic418967fa.accept_19_4_15_9_1_8845 4 129 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 256
  (Polychromatic418967fa.accept_10_3_9_6_1_94 3 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 129 256 (accept_3_3 2 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  129 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 129 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 129
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 128 256 (allA_of_3_1 128 128 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 127 256
  (allA_succ_of_accept 126 127 256 (Polychromatic418967fa.accept_15_6_7_1_1_93 126 127 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 127 256 (accept_3_3 125 127 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 124 127 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 124 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 123 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 127 256 (accept_3_3 122 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 127 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 121 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 127 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 120 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 127 256 (accept_3_3 119 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 127 256 (Polychromatic418967fa.accept_11_8_6_3_1_661 118 127
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 117 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 127 256 (accept_3_3 116 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 127 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 115 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 127 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 114 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 127 256 (accept_3_3 113 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 127 256 (Polychromatic418967fa.accept_19_17_13_9_1_5970 112
  127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 127 256 (accept_3_3 110 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 127 256 (Polychromatic418967fa.accept_14_11_1_4_1_4445 109 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 127 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 108 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 127 256 (accept_3_3 107 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 127 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 106 127
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 127 256 (accept_3_3 104 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 127 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 103 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 127 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 102 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 127 256 (accept_3_3 101 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 127 256 (Polychromatic418967fa.accept_15_10_7_1_1_3686 100
  127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 127 256 (accept_3_3 98 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 127 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 97 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 127 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 96 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 127 256 (accept_3_3 95 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 127 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 94 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 127 256 (accept_3_3 92 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 127 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 91 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 127 256 (Polychromatic418967fa.accept_13_12_10_9_1_1166 90 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 127 256 (accept_3_3 89 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 127 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 127 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 127 256 (accept_3_3 86 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 127 256 (Polychromatic418967fa.accept_11_8_6_3_1_661 85 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 127 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 127 256 (accept_3_3 83 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 127 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 82 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 127 256 (accept_3_3 80 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 127 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 127 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 78 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 127 256 (accept_3_3 77 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 127 256 (Polychromatic418967fa.accept_21_13_1_4_1_11182 76 127 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 127 256 (accept_3_3 74 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 127 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 127 256 (Polychromatic418967fa.accept_17_4_8_1_1_5740 72 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 127 256 (accept_3_3 71 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 127 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 127 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 127 256 (accept_3_3 68 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 127 256 (Polychromatic418967fa.accept_14_11_1_4_1_4445 67 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 127 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 256 (accept_3_3 65 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 127 256 (Polychromatic418967fa.accept_11_9_6_3_1_1668 64 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 127 256 (accept_3_3 62 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 127 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 127 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 127 256 (accept_3_3 59 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 127 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 127 256 (accept_3_3 56 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 127 256 (Polychromatic418967fa.accept_15_10_7_1_1_3686 55 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 127 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 127 256 (accept_3_3 53 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 127 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 127 256 (accept_3_3 50 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 127 256 (Polychromatic418967fa.accept_20_9_7_16_1_4030 49 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 127 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 256 (accept_3_3 47 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 127 256 (accept_3_3 44 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 127 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 127 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 256 (accept_3_3 41 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 127 256 (accept_3_3 38 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 127 256 (Polychromatic418967fa.accept_19_18_13_9_1_5971 37 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 127 256 (Polychromatic418967fa.accept_15_6_7_1_1_93 36 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 256 (accept_3_3 35 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 127 256 (accept_3_3 32 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 127 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 127 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 256 (accept_3_3 29 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 256 (Polychromatic418967fa.accept_17_11_8_1_1_3362 28 127 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 127 256 (accept_3_3 26 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 127 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 127 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 256 (accept_3_3 23 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 256 (accept_3_3 20 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 256 (Polychromatic418967fa.accept_19_18_13_9_1_5971 18 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 256 (accept_3_3 17 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 127 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 256 (accept_3_3 14 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 256 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 256 (accept_3_3 11 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 256 (accept_3_3 8 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 256 (accept_3_3 5 127 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 256 (Polychromatic418967fa.accept_17_4_8_1_1_5740 4 127 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 256 (accept_3_3 2 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 127 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127
  256)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 126 256 (allA_succ_of_accept 125 126 256 (accept_3_3 125 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 126 256 2 62 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 126 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 123 126 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 126 256 2 61 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 126 256
  (Polychromatic418967fa.accept_20_1_6_16_1_6991 121 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 120 126 256 2 60 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 119 126 256 (accept_3_3 119 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 126 256 2 59 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 126 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 117 126 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 126 256 2 58 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 126 256
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 115 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 126 256 2 57 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 126 256 (accept_3_3 113 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 126 256 2 56 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 126 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 111 126 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 126 256 2 55 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 126 256
  (Polychromatic418967fa.accept_19_14_12_9_1_4587 109 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 126 256 2 54 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 126 256 (accept_3_3 107 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 126 256 2 53 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 126 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 105 126 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 126 256 2 52 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 126 256
  (Polychromatic418967fa.accept_25_3_1_6_1_11993 103 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 126 256 2 51 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 126 256 (accept_3_3 101 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 126 256 2 50 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 126 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 99 126 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 126 256 2 49 63 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 126 256
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 97 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 126 256 2 48 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 126 256 (accept_3_3 95 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 126 256 2 47 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 126 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 93 126 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 126 256 2 46 63 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 126 256
  (Polychromatic418967fa.accept_20_11_6_16_1_8481 91 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 126 256 2 45 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 126 256 (accept_3_3 89 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 126 256 2 44 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 126 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 87 126 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 126 256 2 43 63 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 126 256
  (Polychromatic418967fa.accept_11_8_5_3_1_694 85 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 126 256 2 42 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 126 256 (accept_3_3 83 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 126 256 2 41 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 126 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 81 126 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 126 256 2 40 63 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 126 256
  (Polychromatic418967fa.accept_17_11_7_1_1_7023 79 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 256 2 39 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 256 (accept_3_3 77 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 126 256 2 38 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 126 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 75 126 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 126 256 2 37 63 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 126 256
  (Polychromatic418967fa.accept_19_16_12_9_1_10223 73 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 126 256 2 36 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 126 256 (accept_3_3 71 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 126 256 2 35 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 126 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 126 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 126 256 2 34 63 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 126 256
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 67 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 256 2 33 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 256 (accept_3_3 65 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 126 256 2 32 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 126 256 (Polychromatic418967fa.accept_11_8_5_3_1_694 63 126 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 126 256 2 31 63 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 126 256
  (Polychromatic418967fa.accept_17_10_7_1_1_7024 61 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 256 2 30 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 256 (accept_3_3 59 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 126 256 2 29 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 126 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 126 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 126 256 2 28 63 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 126 256
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 55 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 256 2 27 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 256 (accept_3_3 53 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 126 256 2 26 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 126 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 126 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 126 256 2 25 63 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 126 256
  (Polychromatic418967fa.accept_22_5_16_14_1_9386 49 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 126 256 2 24 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 126 256 (accept_3_3 47 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 126 256 2 23 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 126 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 126 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 126 256 2 22 63 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 256
  (Polychromatic418967fa.accept_19_5_12_9_1_4588 43 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 256 2 21 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 256 (accept_3_3 41 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 126 256 2 20 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 126 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 126 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 126 256 2 19 63 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 256
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 37 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 256 2 18 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 256 (accept_3_3 35 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 126 256 2 17 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 126 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 126 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 126 256 2 16 63 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 256
  (Polychromatic418967fa.accept_20_11_6_16_1_8481 31 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 126 256 2 15 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 126 256 (accept_3_3 29 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 126 256 2 14 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 126 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 126 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 126 256 2 13 63 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 256
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 25 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 256 2 12 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 256 (accept_3_3 23 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 126 256 2 11 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 126 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 126 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 126 256 2 10 63 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 256
  (Polychromatic418967fa.accept_11_8_5_3_1_694 19 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 256 2 9 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 126 256 (accept_3_3 17 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 126 256 2 8 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 126 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 126 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 126 256 2 7 63 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 256
  (Polychromatic418967fa.accept_22_13_16_14_1_11030 13 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 126 256 2 6 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 126 256 (accept_3_3 11 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 126 256 2 5 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 126 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 126 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 256 2 4 63 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 256
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 256 2 3 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 256 (accept_3_3 5 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126
  256 2 2 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  126 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 126 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 126 256 2 1 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 126 256 (Polychromatic418967fa.accept_19_1_12_9_1_11621 1 126 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 125 256 (allA_of_3_1 125 125 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 124 256
  (allA_succ_of_accept 123 124 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 123 124 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 124 256 2 61 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 124 256 (Polychromatic418967fa.accept_7_2_5_4_1_115
  121 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 124 256 4 30 31 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 124 256
  (accept_3_3 119 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 124 256 2 59 62 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 124 256
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 117 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 124 256 4 29 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 124 256 (Polychromatic418967fa.accept_10_5_4_6_1_319 115 124 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 124 256 2 57 62 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 124 256 (accept_3_3 113 124 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 124 256 4 28 31 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 124 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 111 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 124 256 2 55 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 124 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 109 124 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 124 256 4 27 31 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 124 256 (accept_3_3 107 124 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 124 256 2 53 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 124 256 (Polychromatic418967fa.accept_9_6_7_4_1_212
  105 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 124 256 4 26 31 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 124 256
  (Polychromatic418967fa.accept_27_22_16_13_1_13701 103 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 124 256 2 51 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 124 256 (accept_3_3 101 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 124 256 4 25 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 124 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 99 124 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 124 256 2 49 62 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 124 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 97 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 124 256 4 24 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 124 256 (accept_3_3 95 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 124 256 2 47 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 124 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 93 124 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 124 256 4 23 31 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 124 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 91 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 124 256 2 45 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 124 256 (accept_3_3 89 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 124 256 4 22 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 124 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 87 124 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 124 256 2 43 62 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 124 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 85 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 124 256 4 21 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 124 256 (accept_3_3 83 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 124 256 2 41 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 124 256 (Polychromatic418967fa.accept_13_3_7_9_1_1153 81 124 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 124 256 4 20 31 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 124 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 79 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 124 256 2 39 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 124 256 (accept_3_3 77 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 124 256 4 19 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 124 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 75 124 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 124 256 2 37 62 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 124 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 73 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 124 256 4 18 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 124 256 (accept_3_3 71 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 124 256 2 35 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 124 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 124 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 124 256 4 17 31 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 124 256
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 67 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 124 256 2 33 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 124 256 (accept_3_3 65 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 124 256 4 16 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 124 256 (Polychromatic418967fa.accept_13_11_7_9_1_612 63 124 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 124 256 2 31 62 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 124 256
  (Polychromatic418967fa.accept_18_7_16_4_1_1674 61 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 124 256 4 15 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 124 256 (accept_3_3 59 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 124 256 2 29 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 124 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 124 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 124 256 4 14 31 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 124 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 55 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 124 256 2 27 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 124 256 (accept_3_3 53 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 124 256 4 13 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 124 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 124 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 124 256 2 25 62 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 124 256
  (Polychromatic418967fa.accept_21_7_19_4_1_4956 49 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 124 256 4 12 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 124 256 (accept_3_3 47 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 124 256 2 23 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 124 256 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 124 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 256 4 11 31 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 124 256 2 21 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 124 256 (accept_3_3 41 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 256 4 10 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 124 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 256 2 19 62 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 256 4 9 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 124 256 (accept_3_3 35 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  124 256 2 17 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 124 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 124 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 256 4 8 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 256
  (Polychromatic418967fa.accept_19_12_10_9_1_3326 31 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 124 256 2 15 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 124 256 (accept_3_3 29 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 124 256 4 7 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 124 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 124 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 124 256 2 13 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 124 256 (Polychromatic418967fa.accept_10_5_4_6_1_319
  25 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 124 256 4 6 31 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 124 256
  (accept_3_3 23 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 124 256 2 11 62 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 124 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 124 256 4 5 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 124 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 124 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 124 256 2 9 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 124 256 (accept_3_3 17 124 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 124 256 4 4 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 124 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 124 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 124 256 2 7 62 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 124 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 124 256 4 3 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 124 256 (accept_3_3 11 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  124 256 2 5 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 124 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 124 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 256 4 2 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 256 (Polychromatic418967fa.accept_18_7_16_4_1_1674 7 124 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 256 2 3 62 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 256 (accept_3_3 5
  124 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124 256 4 1 31 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 124 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 124 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 124 256 2 1 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 124 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 124 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 124
  256))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_256_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


