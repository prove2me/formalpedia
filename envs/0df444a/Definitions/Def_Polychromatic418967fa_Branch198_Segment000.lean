-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch198_Segment000
-- name    : Polychromatic418967fa_Branch198_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:29:47.643622+00:00
-- url     : https://prove2.me/theorems/4082115f-024a-461a-9597-ee4ba0374ded
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_198_segment_000 : allB 101 198 :=
  allB_succ' 99 100 198 (Eq.refl Bool.true) (allA_succ_of_gcd 98 100 198 2 49 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 100 198
  (Polychromatic418967fa.accept_13_6_9_3_1_915 97 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 100 198 2 48 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 100 198 (accept_3_5 95 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 100 198 2 47 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 100 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 93 100 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 100 198 2 46 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 100 198
  (Polychromatic418967fa.accept_16_11_4_6_1_4422 91 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 100 198 2 45 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 100 198 (accept_3_5 89 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 100 198 2 44 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 100 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 87 100 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 100 198 2 43 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 100 198
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 85 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 100 198 2 42 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 100 198 (accept_3_5 83 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 100 198 2 41 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 100 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 81 100 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 100 198 2 40 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 100 198
  (Polychromatic418967fa.accept_19_3_5_8_1_8790 79 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 100 198 2 39 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 100 198 (accept_3_5 77 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 100 198 2 38 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 100 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 75 100 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 100 198 2 37 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 100 198
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 73 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 100 198 2 36 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 100 198 (accept_3_5 71 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 100 198 2 35 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 100 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 69 100 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 100 198 2 34 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 100 198
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 67 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 100 198 2 33 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 100 198 (accept_3_5 65 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 100 198 2 32 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 100 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 100 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 100 198 2 31 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 100 198
  (Polychromatic418967fa.accept_16_13_4_6_1_2322 61 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 100 198 2 30 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 100 198 (accept_3_5 59 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 100 198 2 29 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 100 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 57 100 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 100 198 2 28 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 100 198
  (Polychromatic418967fa.accept_17_4_15_11_1_6465 55 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 100 198 2 27 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 100 198 (accept_3_5 53 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 100 198 2 26 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 100 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 51 100 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 198 2 25 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 198
  (Polychromatic418967fa.accept_21_7_16_9_1_2417 49 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 100 198 2 24 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 100 198 (accept_3_5 47 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 100 198 2 23 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 100 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 100 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 100 198 2 22 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 100 198
  (Polychromatic418967fa.accept_15_13_10_3_1_1952 43 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 100 198 2 21 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 100 198 (accept_3_5 41 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 100 198 2 20 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 100 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 100 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 100 198 2 19 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 100 198
  (Polychromatic418967fa.accept_15_7_10_3_1_2891 37 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 100 198 2 18 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 100 198 (accept_3_5 35 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 100 198 2 17 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 100 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 100 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 100 198 2 16 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 100 198
  (Polychromatic418967fa.accept_13_5_9_3_1_870 31 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 100 198 2 15 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 100 198 (accept_3_5 29 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 100 198 2 14 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 100 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 100 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 198 2 13 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 100 198
  (Polychromatic418967fa.accept_13_12_9_3_1_3047 25 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 100 198 2 12 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 100 198 (accept_3_5 23 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 100 198 2 11 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 100 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 100 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 100 198 2 10 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 198
  (Polychromatic418967fa.accept_13_6_9_3_1_915 19 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 100 198 2 9 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 100 198 (accept_3_5 17 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  100 198 2 8 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 100 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 100 198 2 7 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 100 198 (Polychromatic418967fa.accept_15_13_10_3_1_1952 13 100 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 198 2 6 50 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 198 (accept_3_5 11
  100 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 198 2 5 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 198
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 100 198 2 4 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 100 198 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 100 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 198 2 3 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 100 198 (accept_3_5 5 100 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 100 198 2 2 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 100 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 100 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 198 2 1 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 198 (Polychromatic418967fa.accept_27_1_19_9_1_3593
  1 100 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 99
  198 (allA_succ_of_accept 98 99 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 98 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 99 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 99 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 99 198 3 32 33 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 99 198
  (Polychromatic418967fa.accept_15_5_9_3_1_528 95 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 99 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 94 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 99 198 3 31 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 99 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 92
  99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 99 198
  (Polychromatic418967fa.accept_10_1_9_8_1_123 91 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 99 198 9 10 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 99 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 89 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 99 198 11 8 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 99 198 3 29 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 99 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 86 99 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 85 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 99 198 3 28 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 99 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 82 99 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 99 198 9 9 11 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 99 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 80 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 198 (Polychromatic418967fa.accept_19_3_4_8_1_8808 79 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 99 198 3 26 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 99 198 11 7 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 99 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 76
  99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 99 198 3 25 33 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 99 198
  (Polychromatic418967fa.accept_10_4_9_8_1_125 74 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 99 198 9 8 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 99 198 (Polychromatic418967fa.accept_10_1_9_8_1_123 71 99 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 198
  (Polychromatic418967fa.accept_12_10_3_6_1_882 70 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 99 198 3 23 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 99 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 68 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 198 (Polychromatic418967fa.accept_10_7_9_8_1_1135 67 99 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 198 33 2 3 6 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 99 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 99 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 64 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 99 198 9 7 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 99 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 99 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 61 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 99 198 3 20 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 99 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 58 99 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 99 198 3 19 33 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 99 198
  (Polychromatic418967fa.accept_12_8_3_6_1_909 56 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 99 198 11 5 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 99 198 9 6 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 99 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 99 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 99 198 3 17 33 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 99 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 50 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 99 198 3 16 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 99 198 (Polychromatic418967fa.accept_10_7_9_8_1_1135
  47 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 198
  (Polychromatic418967fa.accept_12_10_3_6_1_882 46 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 99 198 9 5 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 99 198 11 4 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 99 198 (Polychromatic418967fa.accept_15_13_9_3_1_1949 43 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 99 198 3 14 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 99 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 99
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 198
  (Polychromatic418967fa.accept_12_4_3_6_1_879 40 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 99 198 3 13 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 99 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 99 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 198 9 4 11 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 198
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 35 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 99 198 33 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 99 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 99 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 99 198 3 10 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 99 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 99 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 198 9 3 11 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 26 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 99 198 3 8 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 99 198 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 99 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 99 198 11 2 9 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 99 198 3 7 33 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 198 (Polychromatic418967fa.accept_21_19_15_9_1_11533 19 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 198 9 2 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 99 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 198
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 99 198 3 5 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 99 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 99 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 198 3 4 33 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 99 198 11 1 9 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 99 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 10 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 99 198 9 1 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 99 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 198 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 99 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 99 198 3 2 33 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 99 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 99 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 198 3 1 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 99 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 99 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 99 198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 98 198 (allA_succ_of_accept 97 98 198 (accept_3_4 97 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 98 198 2 48 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 98 198 (Polychromatic418967fa.accept_13_4_7_3_1_92 95 98 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 98 198 2 47 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 98 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 93
  98 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 98 198 2 46 49 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 98 198 (accept_3_4 91
  98 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 98 198 2 45 49 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 98 198
  (Polychromatic418967fa.accept_13_11_7_3_1_894 89 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 98 198 2 44 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 87 98 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 87 98 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 98 198 2 43 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 98 198 (accept_3_4 85 98 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98 198 2 42 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 98 198 (Polychromatic418967fa.accept_16_3_2_6_1_4461 83 98 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 98 198 2 41 49 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 98 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 81 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 98 198 2 40 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 98 198 (accept_3_4 79 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 98
  198 2 39 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77
  98 198 (Polychromatic418967fa.accept_23_8_6_14_1_11511 77 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 98 198 2 38 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 98 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 75 98 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 98 198 2 37 49 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 98 198 (accept_3_4 73 98 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 98 198 2 36 49 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 98 198
  (Polychromatic418967fa.accept_15_11_8_3_1_1943 71 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 98 198 2 35 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 98 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 69 98 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 98 198 2 34 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 98 198 (accept_3_4 67 98 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 98 198 2 33 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 98 198 (Polychromatic418967fa.accept_15_5_8_3_1_556 65 98 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 98 198 2 32 49 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 98 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 98 198 2 31 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 98 198 (accept_3_4 61 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 98
  198 2 30 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  98 198 (Polychromatic418967fa.accept_16_11_2_6_1_1435 59 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 98 198 2 29 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 98 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 57 98 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 98 198 2 28 49 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 98 198 (accept_3_4 55 98 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 98 198 2 27 49 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 98 198
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 53 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 98 198 2 26 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 98 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 51 98 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 98 198 2 25 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 98 198 (accept_3_4 49 98 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 98 198 2 24 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 98 198 (Polychromatic418967fa.accept_13_8_7_3_1_430 47 98 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 198 2 23 49 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 98 198 2 22 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 98 198 (accept_3_4 43 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98
  198 2 21 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  98 198 (Polychromatic418967fa.accept_15_11_8_3_1_1943 41 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 98 198 2 20 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 98 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 39 98 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 98 198 2 19 49 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 98 198 (accept_3_4 37 98 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 98 198 2 18 49 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 98 198
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 35 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 98 198 2 17 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 98 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 33 98 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 98 198 2 16 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 98 198 (accept_3_4 31 98 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 98 198 2 15 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 98 198 (Polychromatic418967fa.accept_17_12_13_11_1_2910 29 98
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 198 2 14 49 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 198 2 13 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 98 198 (accept_3_4 25 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98
  198 2 12 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  98 198 (Polychromatic418967fa.accept_13_10_7_3_1_3041 23 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 98 198 2 11 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 98 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 98 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 98 198 2 10 49 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 98 198 (accept_3_4 19 98 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98 198 2 9 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 98 198 (Polychromatic418967fa.accept_13_4_7_3_1_92 17
  98 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 198 2 8 49 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 98 198 2 7 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 98 198 (accept_3_4 13 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98
  198 2 6 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  98 198 (Polychromatic418967fa.accept_13_11_7_3_1_894 11 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 98 198 2 5 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 98 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 98 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 198 2 4 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 198 (accept_3_4 7 98 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 198 2 3 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 98 198 (Polychromatic418967fa.accept_15_5_8_3_1_556 5 98 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 198 2 2 49 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 98 198 2 1 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 98 198 (accept_3_4 1 98 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  198 (allA_succ_of_accept 96 97 198 (Polychromatic418967fa.accept_13_5_6_3_1_868 96 97 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 198 (accept_3_5 95 97 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 97 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 94 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 198 (Polychromatic418967fa.accept_30_3_7_18_1_7107
  93 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 198 (accept_3_5 92
  97 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 91 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 97 198 (Polychromatic418967fa.accept_19_14_2_8_1_5925 90 97 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 97 198 (accept_3_5 89 97 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 97 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 88 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 97 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 87
  97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 198 (accept_3_5 86 97
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 198 (Polychromatic418967fa.accept_7_1_6_2_1_18
  85 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 198
  (Polychromatic418967fa.accept_17_16_12_11_1_6504 84 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 97 198 (accept_3_5 83 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 97 198 (Polychromatic418967fa.accept_16_2_1_6_1_2342 82 97 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 97 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 97 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 198 (accept_3_5 80 97 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 79
  97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 78 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 198 (accept_3_5 77 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 198 (Polychromatic418967fa.accept_25_1_22_23_1_11557 76 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 198 (accept_3_5 74 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 73 97 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 198
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 72 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 198 (accept_3_5 71 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 198 (Polychromatic418967fa.accept_13_5_6_3_1_868 70 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 69 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 198 (accept_3_5 68 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 97 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 66 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 198 (accept_3_5 65 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 198 (accept_3_5 62 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 198 (Polychromatic418967fa.accept_13_9_6_3_1_1514 61 97 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 198 (accept_3_5 59 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 198 (Polychromatic418967fa.accept_19_1_2_8_1_10129 58 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 198 (accept_3_5 56 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 97 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 198
  (Polychromatic418967fa.accept_21_12_13_9_1_2482 54 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 198 (accept_3_5 53 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 198 (accept_3_5 50 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 49 97 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 198
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 48 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 198 (accept_3_5 47 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 198 (accept_3_5 44 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 97 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 198
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 42 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 198 (accept_3_5 41 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 198 (Polychromatic418967fa.accept_13_1_6_3_1_1547 40 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 198 (accept_3_5 38 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 198 (Polychromatic418967fa.accept_16_5_1_6_1_3367 37 97 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 198 (accept_3_5 35 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 198 (Polychromatic418967fa.accept_15_4_7_3_1_119 34 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 198 (Polychromatic418967fa.accept_17_16_12_11_1_6504 33 97 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 198 (accept_3_5 32 97 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 97 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 198
  (Polychromatic418967fa.accept_17_13_12_11_1_2947 30 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 97 198 (accept_3_5 29 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 97 198 (Polychromatic418967fa.accept_21_7_13_9_1_6937 28 97 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 97 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 198 (accept_3_5 26 97 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 25
  97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 198 (accept_3_5 23 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 198 (Polychromatic418967fa.accept_16_5_1_6_1_3367 21 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 198 (accept_3_5 20 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 97 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 198 (accept_3_5 17 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 198 (Polychromatic418967fa.accept_17_16_12_11_1_6504 16 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 198 (accept_3_5 14 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 198 (Polychromatic418967fa.accept_17_13_12_11_1_2947 13 97 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 198
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 198 (accept_3_5 11 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 198 (accept_3_5 8 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 97 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 198
  (Polychromatic418967fa.accept_17_6_12_11_1_5231 6 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 198 (accept_3_5 5 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  198 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 97 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 97 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 198 (accept_3_5 2 97 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 97 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 198
  (allA_succ_of_accept 95 96 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 95 96 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 96 198 2 47 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 96 198 3 31 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 96 198 2 46 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 96 198 (Polychromatic418967fa.accept_14_7_12_2_1_2502
  91 96 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 198 6 15 16 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 198
  (Polychromatic418967fa.accept_13_11_5_3_1_889 89 96 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 96 198 2 44 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 87 96 198 3 29 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 86 96 198 2 43 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 85 96 198 (Polychromatic418967fa.accept_15_10_6_3_1_1160 85 96 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 198 6 14 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169
  83 96 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 198 2 41 48 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 96 198 3 27 32 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 96 198 2 40 48 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 198
  (Polychromatic418967fa.accept_13_1_5_3_1_888 79 96 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 96 198 6 13 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 96 198 (Polychromatic418967fa.accept_14_7_12_2_1_2502 77 96 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 96 198 2 38 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 96 198 3 25 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 96 198 2 37 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 96 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 73
  96 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 198 6 12 16 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 198
  (Polychromatic418967fa.accept_13_6_5_3_1_426 71 96 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 96 198 2 35 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 96 198 3 23 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 96 198 2 34 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 96 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 67 96 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 198 6 11 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 198 (Polychromatic418967fa.accept_15_5_6_3_1_525 65
  96 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 96 198 2 32 48 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 96 198 3 21 32 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 96 198 2 31 48 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 198
  (Polychromatic418967fa.accept_13_9_5_3_1_428 61 96 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 198 6 10 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 96 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 96 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96 198 2 29 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 96 198 3 19 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 96 198 2 28 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96 198 (Polychromatic418967fa.accept_15_10_6_3_1_1160
  55 96 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 198 6 9 16 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 96 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 96 198 2 26 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 96 198 3 17 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 96 198 2 25 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 96 198 (Polychromatic418967fa.accept_14_7_12_2_1_2502 49 96 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 198 6 8 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 198 (Polychromatic418967fa.accept_13_8_5_3_1_427 47 96 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 198 2 23 48 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 96 198 3 15 32 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 96 198 2 22 48 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 198
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 96 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 198 6 7 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 96 198 (Polychromatic418967fa.accept_13_2_5_3_1_406 41 96 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96 198 2 20 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 96 198 3 13 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 96 198 2 19 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 198 (Polychromatic418967fa.accept_13_11_5_3_1_889
  37 96 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 198 6 6 16 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 198
  (Polychromatic418967fa.accept_13_9_5_3_1_428 35 96 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 96 198 2 17 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 96 198 3 11 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 96 198 2 16 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 96 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 96 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 198 6 5 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 198 (Polychromatic418967fa.accept_21_8_12_9_1_9980 29 96 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 198 2 14 48 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 96 198 3 9 32 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 96 198 2 13 48 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 96 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 198 6 4 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 96 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 198 2 11 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 96 198 3 7 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 96 198 2 10 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 198 (Polychromatic418967fa.accept_13_6_5_3_1_426 19
  96 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 198 6 3 16 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 96 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 96 198 2 8 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 96 198 3 5 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 96 198 2 7 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 96 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 96 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 198 6 2 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 96 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 198 2 5 48 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 96 198 3 3 32 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 96 198 2 4 48 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 198
  (Polychromatic418967fa.accept_14_7_12_2_1_2502 7 96 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 96 198 6 1 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 96 198 (Polychromatic418967fa.accept_15_5_6_3_1_525 5 96 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 198 2 2 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 96 198 3 1 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 96 198 2 1 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 198 (Polychromatic418967fa.accept_13_1_5_3_1_888 1 96 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 198
  (allA_succ_of_accept 94 95 198 (accept_3_4 94 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 92 95 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 198 (accept_3_4 91 95 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 90 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 198 (accept_3_4 88 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 198 (Polychromatic418967fa.accept_10_7_5_8_1_1167 87 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 198 (Polychromatic418967fa.accept_17_1_10_11_1_2943 86 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 198 (accept_3_4 85 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 198 (Polychromatic418967fa.accept_15_9_5_3_1_554 84 95 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 83 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 198 (accept_3_4 82 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 198 (Polychromatic418967fa.accept_23_11_3_14_1_11556 80 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 198 (accept_3_4 79 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 198 (Polychromatic418967fa.accept_21_15_11_9_1_2470 78 95
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 198 (accept_3_4 76 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 198 (Polychromatic418967fa.accept_27_20_14_9_1_9673 74 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 198 (accept_3_4 73 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 72 95 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 198
  (Polychromatic418967fa.accept_16_7_15_6_1_1428 71 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 198 (accept_3_4 70 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 95 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 198 (accept_3_4 67 95 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 198 (Polychromatic418967fa.accept_13_1_4_3_1_1545 66 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 198 (accept_3_4 64 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 198 (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 95 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 198 (accept_3_4 61 95 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 198 (Polychromatic418967fa.accept_21_18_11_9_1_6956 60 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 198
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 59 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 198 (accept_3_4 58 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 198 (Polychromatic418967fa.accept_20_16_15_18_1_5605 56 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 198 (accept_3_4 55 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 95 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 198 (accept_3_4 52 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 198 (Polychromatic418967fa.accept_13_12_4_3_1_1528 51 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 198 (Polychromatic418967fa.accept_20_10_15_18_1_7100 50 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 198 (accept_3_4 49 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 95 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 198 (accept_3_4 46 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 198 (Polychromatic418967fa.accept_21_2_11_9_1_2534 44 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 198 (accept_3_4 43 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 95 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 198 (accept_3_4 40 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 198 (Polychromatic418967fa.accept_15_9_5_3_1_554 39 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 198 (Polychromatic418967fa.accept_13_12_4_3_1_1528 38 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 198 (accept_3_4 37 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 198 (Polychromatic418967fa.accept_15_6_5_3_1_1988 36 95 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 198
  (Polychromatic418967fa.accept_17_1_10_11_1_2943 35 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 198 (accept_3_4 34 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 95 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 198 (accept_3_4 31 95 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 198 (Polychromatic418967fa.accept_20_10_15_18_1_7100 30 95 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 198 (accept_3_4 28 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 95 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 198 (accept_3_4 25 95 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 198 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 198
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 198 (accept_3_4 22 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 95 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 198 (accept_3_4 19 95 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 198 (Polychromatic418967fa.accept_17_1_10_11_1_2943 18 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 198 (accept_3_4 16 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 198 (Polychromatic418967fa.accept_21_15_11_9_1_2470 15 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 198 (Polychromatic418967fa.accept_13_1_4_3_1_1545 14 95 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 198 (accept_3_4 13 95 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 95 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 198
  (Polychromatic418967fa.accept_23_11_3_14_1_11556 11 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 95 198 (accept_3_4 10 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 95 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 95 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 198 (Polychromatic418967fa.accept_15_8_5_3_1_1990 8 95 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 198 (accept_3_4 7 95 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 6
  95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 198 (accept_3_4 4 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  198 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 95 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 95 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 95 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 198 (accept_3_4 1 95 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 95
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 198
  (allA_succ_of_accept 93 94 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 93 94 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 94 198 2 46 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 94 198 (Polychromatic418967fa.accept_15_1_4_3_1_1928
  91 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 94 198 2 45 47 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 94 198 (accept_3_5 89
  94 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 94 198 2 44 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 94 198
  (Polychromatic418967fa.accept_12_3_10_6_1_442 87 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 94 198 2 43 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 85 94 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 85 94 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 94 198 2 42 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 94 198 (accept_3_5 83 94 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 82 94 198 2 41 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 94 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 81 94 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 94 198 2 40 47 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 94 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 79 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 94 198 2 39 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 94 198 (accept_3_5 77 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 94
  198 2 38 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75
  94 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 94 198 2 37 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 94 198 (Polychromatic418967fa.accept_19_16_18_8_1_8784 73 94 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 94 198 2 36 47 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 94 198 (accept_3_5 71 94 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 94 198 2 35 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 94 198
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 94 198 2 34 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 94 198 (Polychromatic418967fa.accept_15_7_4_3_1_1930 67 94 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 94 198 2 33 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 94 198 (accept_3_5 65 94 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 94 198 2 32 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 94 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 63 94 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 94 198 2 31 47 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 94 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 61 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 94 198 2 30 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 94 198 (accept_3_5 59 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 94
  198 2 29 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  94 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 94 198 2 28 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 94 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 94 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 94 198 2 27 47 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 94 198 (accept_3_5 53 94 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 94 198 2 26 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 94 198
  (Polychromatic418967fa.accept_12_3_10_6_1_442 51 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 94 198 2 25 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 94 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 49 94 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 94 198 2 24 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 94 198 (accept_3_5 47 94 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 94 198 2 23 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 94 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 94 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 94 198 2 22 47 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 94 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 94 198 2 21 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 94 198 (accept_3_5 41 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 94
  198 2 20 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  94 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 94 198 2 19 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 94 198 (Polychromatic418967fa.accept_15_7_4_3_1_1930 37 94 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 94 198 2 18 47 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 94 198 (accept_3_5 35 94 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 94 198 2 17 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 94 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 94 198 2 16 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 94 198 (Polychromatic418967fa.accept_15_1_4_3_1_1928 31 94 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 94 198 2 15 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 94 198 (accept_3_5 29 94 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 94 198 2 14 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 94 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 94 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 94 198 2 13 47 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 94 198
  (Polychromatic418967fa.accept_17_8_9_11_1_3976 25 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 94 198 2 12 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 94 198 (accept_3_5 23 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94
  198 2 11 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  94 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 94 198 2 10 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 94 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 94 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 94 198 2 9 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 94 198 (accept_3_5 17 94 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94 198 2 8 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 94 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 94 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 94 198 2 7 47 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 94 198
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 94 198 2 6 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 94 198 (accept_3_5 11 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94
  198 2 5 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  94 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 94 198 2 4 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 94 198 (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 94 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 198 2 3 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 198 (accept_3_5 5 94 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 94 198 2 2 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 94 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 94 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 198 2 1 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 94 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 93 198 (allA_succ_of_accept 92 93 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 92 93 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 91 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 93 198 3 30 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 93 198 (Polychromatic418967fa.accept_13_11_2_3_1_883 89 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 88 93 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 93 198 3 29 31 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 93 198
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 86 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165 85 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 93 198 3 28 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 93 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 83
  93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 198
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 82 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 93 198 3 27 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 93 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 80 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 93 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 93 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 93 198 3 26 31 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 93 198
  (Polychromatic418967fa.accept_13_12_2_3_1_1527 77 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 93 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 76 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 93 198 3 25 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 93 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 74
  93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 198
  (Polychromatic418967fa.accept_16_9_13_6_1_2334 73 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 93 198 3 24 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 93 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 70 93
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 93 198 3 23 31 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 93 198
  (Polychromatic418967fa.accept_12_8_9_6_1_127 68 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 93 198 3 22 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 93 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165
  65 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 64 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 93 198 3 21 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 93 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 62 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 93 198 (Polychromatic418967fa.accept_10_1_3_8_1_136 61 93 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 93 198 3 20 31 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 93 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 93 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 58 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 93 198 3 19 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 93 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660
  56 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 93 198 3 18 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 93 198 (Polychromatic418967fa.accept_13_1_2_3_1_911 53 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 52 93 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 198 3 17 31 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 198
  (Polychromatic418967fa.accept_12_2_9_6_1_439 50 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 198 (Polychromatic418967fa.accept_13_10_2_3_1_3025 49 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 93 198 3 16 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 93 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 198
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 46 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 93 198 3 15 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 93 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 93 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 198 3 14 31 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 198
  (Polychromatic418967fa.accept_10_1_3_8_1_136 41 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 93 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 93 198 3 13 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 93 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 38
  93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 198
  (Polychromatic418967fa.accept_13_11_2_3_1_883 37 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 93 198 3 12 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 93 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 93
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 198 3 11 31 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 198
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 93 198 3 10 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 93 198 (Polychromatic418967fa.accept_19_10_17_8_1_5917
  29 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 93 198 3 9 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 93 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 93 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 198 3 8 31 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 93 198 3 7 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 93 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 93 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 93 198 3 6 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 93 198 (Polychromatic418967fa.accept_25_17_18_23_1_11555 17 93 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660
  16 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 198 3 5 31 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 198
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 198 (Polychromatic418967fa.accept_23_13_1_14_1_11554 13 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 93 198 3 4 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 93 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 93 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 198
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 93 198 3 3 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 93 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 93 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 198 3 2 31 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 198
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 93 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 198 3 1 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 93 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 198
  (Polychromatic418967fa.accept_10_1_3_8_1_136 1 93 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 93 198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 92 198 (allA_succ_of_accept 91 92 198 (accept_3_4 91 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 92 198 2 45 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 92 198 (Polychromatic418967fa.accept_13_11_1_3_1_910 89 92 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 92 198 2 44 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 92 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 87
  92 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 92 198 2 43 46 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 92 198 (accept_3_4 85
  92 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 92 198 2 42 46 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 92 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 83 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 92 198 2 41 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 81 92 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 81 92 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 92 198 2 40 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 92 198 (accept_3_4 79 92 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 78 92 198 2 39 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 92 198 (Polychromatic418967fa.accept_19_1_16_8_1_10075 77 92
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 92 198 2 38 46 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 92 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 75 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 92 198 2 37 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 92 198 (accept_3_4 73 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 92
  198 2 36 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71
  92 198 (Polychromatic418967fa.accept_13_6_1_3_1_1522 71 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 92 198 2 35 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 92 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 92 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 92 198 2 34 46 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 92 198 (accept_3_4 67 92 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 92 198 2 33 46 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 92 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 65 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 92 198 2 32 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 92 198 (Polychromatic418967fa.accept_12_3_8_6_1_895 63 92 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 92 198 2 31 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 92 198 (accept_3_4 61 92 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92 198 2 30 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 92 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 92 198 2 29 46 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 92 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 57 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 92 198 2 28 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 92 198 (accept_3_4 55 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92
  198 2 27 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  92 198 (Polychromatic418967fa.accept_19_15_16_8_1_11553 53 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 92 198 2 26 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 92 198 (Polychromatic418967fa.accept_12_3_8_6_1_895 51 92 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 92 198 2 25 46 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 92 198 (accept_3_4 49 92 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92 198 2 24 46 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 92 198
  (Polychromatic418967fa.accept_17_13_7_11_1_3985 47 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 92 198 2 23 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 92 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 92 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 198 2 22 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 198 (accept_3_4 43 92 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 198 2 21 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 92 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 92 198 2 20 46 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 92 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 92 198 2 19 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 92 198 (accept_3_4 37 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92
  198 2 18 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  92 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 92 198 2 17 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 92 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 33 92 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 92 198 2 16 46 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 92 198 (accept_3_4 31 92 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92 198 2 15 46 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 92 198
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 29 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 92 198 2 14 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 92 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 92 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 198 2 13 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 198 (accept_3_4 25 92 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 198 2 12 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 92 198 (Polychromatic418967fa.accept_32_23_28_6_1_11552 23 92
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 198 2 11 46 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 198 2 10 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 92 198 (accept_3_4 19 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92
  198 2 9 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  92 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 92 198 2 8 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 92 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 92 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 198 2 7 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 198 (accept_3_4 13 92 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 198 2 6 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 92 198 (Polychromatic418967fa.accept_13_11_1_3_1_910 11 92 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 198 2 5 46 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 92 198 2 4 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 92 198 (accept_3_4 7 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 198
  2 3 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92
  198 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 92 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 92 198 2 2 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 92 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 92 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 198 2 1 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 198 (accept_3_4 1 92 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 198
  (allA_succ_of_accept 90 91 198 (Polychromatic418967fa.accept_17_5_6_11_1_3974 90 91 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 198 (accept_3_5 89 91 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 198 (Polychromatic418967fa.accept_15_13_1_3_1_1972 88 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 198
  (Polychromatic418967fa.accept_20_7_11_18_1_7117 87 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 91 198 (accept_3_5 86 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  91 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 91 198 (Polychromatic418967fa.accept_16_4_11_6_1_5591 84 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 91 198 (accept_3_5 83 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 91 198 (Polychromatic418967fa.accept_14_12_7_2_1_1663 82 91
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 91 198 (accept_3_5 80 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  91 198 (Polychromatic418967fa.accept_10_9_1_8_1_755 79 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 91 198 (Polychromatic418967fa.accept_19_2_15_8_1_7306 78 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 198 (accept_3_5 77 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 91 198 (Polychromatic418967fa.accept_20_16_11_18_1_11530 76 91
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 198
  (Polychromatic418967fa.accept_14_5_7_2_1_468 75 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 91 198 (accept_3_5 74 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  91 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 91 198 (Polychromatic418967fa.accept_17_4_6_11_1_1030 72 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 198 (accept_3_5 71 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 91 198 (Polychromatic418967fa.accept_25_20_16_23_1_11497 70 91
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 91 198 (accept_3_5 68 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  91 198 (Polychromatic418967fa.accept_16_3_11_6_1_4467 67 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 91 198 (Polychromatic418967fa.accept_15_6_1_3_1_2852 66 91 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 198 (accept_3_5 65 91 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 91 198 (Polychromatic418967fa.accept_15_4_1_3_1_1922 64 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 198
  (Polychromatic418967fa.accept_10_3_1_8_1_132 63 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 91 198 (accept_3_5 62 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 198 (Polychromatic418967fa.accept_19_3_15_8_1_3232 60 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 198 (accept_3_5 59 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 198 (Polychromatic418967fa.accept_15_13_1_3_1_1972 58 91
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 91 198 (accept_3_5 56 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  91 198 (Polychromatic418967fa.accept_17_4_6_11_1_1030 55 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 91 198 (Polychromatic418967fa.accept_14_12_7_2_1_1663 54 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 198 (accept_3_5 53 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 198 (Polychromatic418967fa.accept_16_4_11_6_1_5591 52 91
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 198
  (Polychromatic418967fa.accept_14_9_7_2_1_2483 51 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 198 (accept_3_5 50 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  91 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 91 198 (Polychromatic418967fa.accept_20_8_11_18_1_11551 48 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 198 (accept_3_5 47 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 198 (Polychromatic418967fa.accept_17_12_6_11_1_7880 46 91
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 198 (accept_3_5 44 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 43 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 198 (Polychromatic418967fa.accept_19_4_15_8_1_5937 42 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 198 (accept_3_5 41 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 198 (Polychromatic418967fa.accept_14_12_7_2_1_1663 40 91
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 198
  (Polychromatic418967fa.accept_10_9_1_8_1_755 39 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 198 (accept_3_5 38 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 198 (Polychromatic418967fa.accept_15_6_1_3_1_2852 36 91 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 198 (accept_3_5 35 91 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 198 (Polychromatic418967fa.accept_15_4_1_3_1_1922 34 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 198 (accept_3_5 32 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 198 (Polychromatic418967fa.accept_19_12_15_8_1_10070 31 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 198 (Polychromatic418967fa.accept_17_13_6_11_1_4014 30 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 198 (accept_3_5 29 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 198 (Polychromatic418967fa.accept_15_13_1_3_1_1972 28 91
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 198
  (Polychromatic418967fa.accept_20_7_11_18_1_7117 27 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 198 (accept_3_5 26 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 198 (Polychromatic418967fa.accept_21_3_7_9_1_8519 24 91 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 198 (accept_3_5 23 91 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 198 (Polychromatic418967fa.accept_17_5_6_11_1_3974 22 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 198 (accept_3_5 20 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 198 (Polychromatic418967fa.accept_10_9_1_8_1_755 19 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 198 (Polychromatic418967fa.accept_16_2_11_6_1_737 18 91 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 198 (accept_3_5 17 91 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 198 (Polychromatic418967fa.accept_19_16_15_8_1_10086 16 91 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 198
  (Polychromatic418967fa.accept_21_15_7_9_1_11550 15 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 198 (accept_3_5 14 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 198 (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 198 (accept_3_5 11 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 198 (Polychromatic418967fa.accept_21_10_7_9_1_11527 10 91
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 198 (accept_3_5 8 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  198 (Polychromatic418967fa.accept_19_7_15_8_1_1089 7 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 91 198 (Polychromatic418967fa.accept_15_6_1_3_1_2852 6 91 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 198 (accept_3_5 5 91 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 198 (Polychromatic418967fa.accept_15_4_1_3_1_1922 4 91 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 198
  (Polychromatic418967fa.accept_10_3_1_8_1_132 3 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 198 (accept_3_5 2 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 91 198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  90 198 (allA_succ_of_accept 89 90 198 (Polychromatic418967fa.accept_19_13_14_8_1_4490 89 90 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 90 198 2 44 45 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 90 198 3 29 30 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 90 198 2 43 45 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 90 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 85 90 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 90 198 6 14 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 90 198 (Polychromatic418967fa.accept_17_15_5_11_1_6468 83 90 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 198 2 41 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 90 198 9 9 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 90 198 2 40 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 198 (Polychromatic418967fa.accept_19_3_14_8_1_3272
  79 90 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 198 6 13 15 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 198
  (Polychromatic418967fa.accept_20_17_10_18_1_4150 77 90 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 90 198 2 38 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 75 90 198 3 25 30 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 90 198 2 37 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 90 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 73 90 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 198 18 4 5 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 90 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 90 198 2 35 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 90 198 3 23 30 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 90 198 2 34 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 90 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 67 90 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 198 6 11 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 198 (Polychromatic418967fa.accept_20_5_10_18_1_5622
  65 90 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 198 2 32 45 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 90 198 9 7 10 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 90 198 2 31 45 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 90 198
  (Polychromatic418967fa.accept_13_9_12_3_1_907 61 90 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 198 6 10 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 90 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 90 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 198 2 29 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 90 198 3 19 30 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 90 198 2 28 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 90 198
  (Polychromatic418967fa.accept_20_15_10_18_1_8658 55 90 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 90 198 18 3 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 90 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 90 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 198 2 26 45 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 90 198 3 17 30 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 90 198 2 25 45 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 198
  (Polychromatic418967fa.accept_17_15_5_11_1_6468 49 90 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 198 6 8 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 90 198 (Polychromatic418967fa.accept_19_9_14_8_1_11549 47 90 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 198 2 23 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 90 198 9 5 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 90 198 2 22 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 43
  90 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 198 6 7 15 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 198
  (Polychromatic418967fa.accept_13_2_12_3_1_415 41 90 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 90 198 2 20 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 90 198 3 13 30 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 90 198 2 19 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 90 198 (Polychromatic418967fa.accept_20_17_10_18_1_4150 37 90 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 198 18 2 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 90 198 (Polychromatic418967fa.accept_13_9_12_3_1_907 35 90 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 198 2 17 45 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 90 198 3 11 30 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 90 198 2 16 45 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 90 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 198 6 5 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 90 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 90 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 198 2 14 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 90 198 9 3 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 90 198 2 13 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 25
  90 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 198 6 4 15 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 198
  (Polychromatic418967fa.accept_17_6_5_11_1_4073 23 90 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 90 198 2 11 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 90 198 3 7 30 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 90 198 2 10 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 90 198 (Polychromatic418967fa.accept_23_19_21_14_1_11548 19 90 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 198 18 1 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 17
  90 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 198 2 8 45 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 198 3 5 30 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 198 2 7 45 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 198
  (Polychromatic418967fa.accept_19_13_14_8_1_4490 13 90 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 90 198 6 2 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 90 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 90 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 198 2 5 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 90 198 9 1 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 90 198 2 4 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 198 (Polychromatic418967fa.accept_17_7_5_11_1_2922 7 90 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 198 6 1 15 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 198
  (Polychromatic418967fa.accept_19_5_14_8_1_5944 5 90 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 90 198 2 2 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 90 198 3 1 30 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 90 198 2 1 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 90 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 90
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 198
  (allA_succ_of_accept 88 89 198 (accept_3_4 88 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 198 (Polychromatic418967fa.accept_13_8_11_3_1_3053 86 89 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 198 (accept_3_4 85 89 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 84 89 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 198 (accept_3_4 82 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 80 89 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 198 (accept_3_4 79 89 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 198 (Polychromatic418967fa.accept_17_10_4_11_1_4047 78 89 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 198
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 77 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 198 (accept_3_4 76 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 74 89 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 198 (accept_3_4 73 89 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 198 (Polychromatic418967fa.accept_13_7_11_3_1_1540 72 89 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 198 (accept_3_4 70 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 198 (Polychromatic418967fa.accept_36_33_17_18_1_11547 69 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 198 (Polychromatic418967fa.accept_27_14_8_9_1_9614 68 89 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 198 (accept_3_4 67 89 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 89 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 198
  (Polychromatic418967fa.accept_25_15_14_23_1_11546 65 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 89 198 (accept_3_4 64 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 89 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 89 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 89 198 (Polychromatic418967fa.accept_13_10_11_3_1_1518 62 89
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 198 (accept_3_4 61 89 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 60
  89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 198 (accept_3_4 58 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 198 (Polychromatic418967fa.accept_10_7_9_8_1_1135 57 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 198 (Polychromatic418967fa.accept_15_11_14_3_1_1965 56 89 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 198 (accept_3_4 55 89 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 89 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 198 (accept_3_4 52 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 198 (Polychromatic418967fa.accept_16_2_9_6_1_4441 50 89 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 198 (accept_3_4 49 89 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 198 (Polychromatic418967fa.accept_26_22_11_16_1_11545 48 89 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 198 (accept_3_4 46 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 44 89 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 198 (accept_3_4 43 89 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 198 (Polychromatic418967fa.accept_19_4_13_8_1_11544 42 89 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 198
  (Polychromatic418967fa.accept_10_1_9_8_1_123 41 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 198 (accept_3_4 40 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 89 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 198 (accept_3_4 37 89 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 198 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 89 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 198 (accept_3_4 34 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 198 (Polychromatic418967fa.accept_13_7_11_3_1_1540 33 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 89 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 198 (accept_3_4 31 89 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 198 (Polychromatic418967fa.accept_23_7_20_14_1_11501 30 89 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 198
  (Polychromatic418967fa.accept_16_13_9_6_1_2306 29 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 198 (accept_3_4 28 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 198 (Polychromatic418967fa.accept_15_11_14_3_1_1965 26 89 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 198 (accept_3_4 25 89 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 89 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 198 (accept_3_4 22 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 198 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 198 (Polychromatic418967fa.accept_13_7_11_3_1_1540 20 89 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 198 (accept_3_4 19 89 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 89 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 198 (accept_3_4 16 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 89 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 198 (accept_3_4 13 89 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 198 (Polychromatic418967fa.accept_21_12_5_9_1_8504 12 89 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 198 (accept_3_4 10 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 198 (Polychromatic418967fa.accept_23_9_20_14_1_9875 9 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 198 (Polychromatic418967fa.accept_13_8_11_3_1_3053 8 89 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 198 (accept_3_4 7 89 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 198 (Polychromatic418967fa.accept_17_6_4_11_1_4072 6 89 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 198
  (Polychromatic418967fa.accept_13_5_11_3_1_902 5 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 198 (accept_3_4 4 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 89 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 198 (Polychromatic418967fa.accept_13_2_11_3_1_873 2 89 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 198 (accept_3_4 1 89 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 198 (allA_succ_of_accept 87 88 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 87 88 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 88 198 2 43 44 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 88 198
  (Polychromatic418967fa.accept_13_7_10_3_1_1505 85 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 88 198 2 42 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 88 198 (accept_3_5 83 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 88
  198 2 41 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81
  88 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 81 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 88 198 2 40 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 88 198 (Polychromatic418967fa.accept_14_9_4_2_1_983 79 88 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 88 198 2 39 44 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 88 198 11 7 8 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 88 198 2 38 44 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 88 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 88 198 2 37 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 88 198 (Polychromatic418967fa.accept_20_13_8_18_1_8672 73 88 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 88 198 2 36 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 88 198 (accept_3_5 71 88 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 88 198 2 35 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 88 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 88 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 88 198 2 34 44 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 88 198
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 67 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 88 198 22 3 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 88 198 (accept_3_5 65 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 88
  198 2 32 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  88 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 88 198 2 31 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 88 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 88 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 88 198 2 30 44 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 88 198 (accept_3_5 59 88 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 88 198 2 29 44 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 88 198
  (Polychromatic418967fa.accept_12_9_4_6_1_460 57 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 88 198 2 28 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 88 198 11 5 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 88 198 2 27 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 88 198 (accept_3_5 53 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 88
  198 2 26 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  88 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 51 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 88 198 2 25 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 88 198 (Polychromatic418967fa.accept_19_11_12_8_1_11492 49 88 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 88 198 2 24 44 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 88 198 (accept_3_5 47 88 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 88 198 2 23 44 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 88 198
  (Polychromatic418967fa.accept_12_9_4_6_1_460 45 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 88 198 22 2 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 88 198 (Polychromatic418967fa.accept_17_9_3_11_1_3983 43 88 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 88 198 2 21 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 88 198 (accept_3_5 41 88 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88 198 2 20 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 88 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 88 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 88 198 2 19 44 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 88 198
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 37 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 88 198 2 18 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 88 198 (accept_3_5 35 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88
  198 2 17 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 88
  198 11 3 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 88
  198 2 16 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31
  88 198 (Polychromatic418967fa.accept_15_1_13_3_1_2002 31 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 88 198 2 15 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 88 198 (accept_3_5 29 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 88 198 2 14 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 88 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 88 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 88 198 2 13 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 198 (Polychromatic418967fa.accept_15_10_13_3_1_4816
  25 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 88 198 2 12 44 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 88 198 (accept_3_5 23
  88 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88 198 22 1 4 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 88 198
  (Polychromatic418967fa.accept_12_9_4_6_1_460 21 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 88 198 2 10 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 88 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 88 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 88 198 2 9 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 88 198 (accept_3_5 17 88 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 88 198 2 8 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 88 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 88 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 88 198 2 7 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 88 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 13
  88 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 198 2 6 44 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 88 198 11 1 8 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 88 198 2 5 44 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 88 198
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 88 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 88 198 2 4 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 88 198 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 88 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 198 2 3 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 198 (accept_3_5 5 88 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 88 198 2 2 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 88 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 88 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 198 2 1 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 198 (Polychromatic418967fa.accept_15_1_13_3_1_2002 1
  88 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 198
  (allA_succ_of_accept 86 87 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 86 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 87 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 87 198 3 28 29 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 87 198
  (Polychromatic418967fa.accept_7_6_3_2_1_461 83 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 82 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 198 3 27 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 80
  87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 198
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 79 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 87 198 3 26 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 87 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 76 87 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 87 198 3 25 29 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 87 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 74 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 198 3 24 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 71
  87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 198
  (Polychromatic418967fa.accept_12_10_3_6_1_882 70 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 87 198 3 23 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 87 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 198 (Polychromatic418967fa.accept_13_2_9_3_1_2212 67 87 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 87 198 3 22 29 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 87 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 64 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 198 3 21 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 62
  87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 61 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 87 198 3 20 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 87 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 59 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 58 87 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 87 198 3 19 29 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 87 198
  (Polychromatic418967fa.accept_12_8_3_6_1_909 56 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 198 3 18 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 87
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 198
  (Polychromatic418967fa.accept_12_4_3_6_1_879 52 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 87 198 3 17 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 87 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 87 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 87 198 3 16 29 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 87 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 46 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 198 3 15 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 44
  87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 87 198 3 14 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 87 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 87 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 87 198 3 13 29 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 87 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 198 3 12 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 198 (Polychromatic418967fa.accept_10_5_7_8_1_1176
  35 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 198
  (Polychromatic418967fa.accept_7_6_3_2_1_461 34 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 87 198 3 11 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 87 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 198 (Polychromatic418967fa.accept_13_5_9_3_1_870 31 87 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 198 3 10 29 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 198 3 9 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 87 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 87 198 3 8 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 87 198 (Polychromatic418967fa.accept_15_8_12_3_1_1912 23 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 87 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 198 3 7 29 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 198
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 198 3 6 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 87 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 198
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 198 3 5 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 87 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 198 3 4 29 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 198
  (Polychromatic418967fa.accept_20_11_7_18_1_8632 11 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 198 3 3 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 87 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 198
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 198 3 2 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 87 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 198 3 1 29 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 87 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 198
  (allA_succ_of_accept 85 86 198 (accept_3_4 85 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 86
  198 2 42 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83
  86 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 83 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 86 198 2 41 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 86 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 81 86 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 86 198 2 40 43 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 86 198 (accept_3_4 79 86 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86 198 2 39 43 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 86 198
  (Polychromatic418967fa.accept_21_14_2_9_1_6864 77 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 86 198 2 38 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 86 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 75 86 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 198 2 37 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 198 (accept_3_4 73 86 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 198 2 36 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 198 (Polychromatic418967fa.accept_25_21_11_23_1_11543 71 86
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 86 198 2 35 43 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 86 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 69 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 86 198 2 34 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 86 198 (accept_3_4 67 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 86
  198 2 33 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  86 198 (Polychromatic418967fa.accept_24_17_14_6_1_11542 65 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 86 198 2 32 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 86 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 86 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 86 198 2 31 43 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 86 198 (accept_3_4 61 86 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 86 198 2 30 43 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 86 198
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 59 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 86 198 2 29 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 86 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 57 86 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 86 198 2 28 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 86 198 (accept_3_4 55 86 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 86 198 2 27 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 86 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 86 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 198 2 26 43 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 51 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 198 2 25 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 86 198 (accept_3_4 49 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 86
  198 2 24 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  86 198 (Polychromatic418967fa.accept_25_22_11_23_1_11541 47 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 86 198 2 23 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 86 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 45 86 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 86 198 2 22 43 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 86 198 (accept_3_4 43 86 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 86 198 2 21 43 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 86 198
  (Polychromatic418967fa.accept_17_7_1_11_1_1894 41 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 86 198 2 20 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 86 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 39 86 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 86 198 2 19 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 86 198 (accept_3_4 37 86 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 86 198 2 18 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 86 198 (Polychromatic418967fa.accept_13_9_8_3_1_3045 35 86 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 198 2 17 43 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 198
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 198 2 16 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 86 198 (accept_3_4 31 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86
  198 2 15 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  86 198 (Polychromatic418967fa.accept_15_14_11_3_1_1957 29 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 86 198 2 14 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 86 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 86 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 86 198 2 13 43 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 86 198 (accept_3_4 25 86 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86 198 2 12 43 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 86 198
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 86 198 2 11 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 86 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 86 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 198 2 10 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 198 (accept_3_4 19 86 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 198 2 9 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 86 198 (Polychromatic418967fa.accept_19_17_10_8_1_5942 17 86 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 198 2 8 43 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 86 198 2 7 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 86 198 (accept_3_4 13 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86
  198 2 6 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  86 198 (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 86 198 2 5 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 86 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 198 2 4 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 198 (accept_3_4 7 86 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 198 2 3 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 86 198 (Polychromatic418967fa.accept_13_5_8_3_1_1535 5 86 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 198 2 2 43 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 198
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 198 2 1 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 198 (accept_3_4 1 86 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 198
  (allA_succ_of_accept 84 85 198 (Polychromatic418967fa.accept_15_9_10_3_1_2845 84 85 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 198 (accept_3_5 83 85 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 82 85 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 198 (Polychromatic418967fa.accept_15_6_10_3_1_2844
  81 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 198 (accept_3_5 80
  85 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 79 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 198 (Polychromatic418967fa.accept_14_8_1_2_1_965 78 85 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 198 (accept_3_5 77 85 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 76 85 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 85 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 75
  85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 198 (accept_3_5 74 85
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 73 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 85 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 72 85 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 85 198 (accept_3_5 71 85 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 85 198 (Polychromatic418967fa.accept_20_10_5_18_1_5627 70 85 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 85 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 85 198 (accept_3_5 68 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  85 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 85 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 85 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 85 198 (accept_3_5 65 85 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 85 198 (Polychromatic418967fa.accept_14_8_1_2_1_965 64 85 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 85 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 85 198 (accept_3_5 62 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  85 198 (Polychromatic418967fa.accept_13_9_7_3_1_1531 61 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 85 198 (Polychromatic418967fa.accept_13_8_7_3_1_430 60 85 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 85 198 (accept_3_5 59 85 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 198 (Polychromatic418967fa.accept_15_13_10_3_1_1952 58 85 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 198
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 57 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 198 (accept_3_5 56 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  85 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 85 198 (Polychromatic418967fa.accept_15_9_10_3_1_2845 54 85 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 198 (accept_3_5 53 85 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 85 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 85 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 85 198 (accept_3_5 50 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  85 198 (Polychromatic418967fa.accept_13_10_7_3_1_3041 49 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 85 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 85 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 198 (accept_3_5 47 85 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 198 (Polychromatic418967fa.accept_24_22_13_6_1_9818 46 85 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 85 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 85 198 (accept_3_5 44 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  85 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 85 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 85 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 198 (accept_3_5 41 85 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 85 198 (Polychromatic418967fa.accept_13_1_7_3_1_1503 40 85 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 85 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 85 198 (accept_3_5 38 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  85 198 (Polychromatic418967fa.accept_10_7_5_8_1_1167 37 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 85 198 (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 85 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 198 (accept_3_5 35 85 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 85 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 85 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 198
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 85 198 (accept_3_5 32 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  85 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 85 198 (Polychromatic418967fa.accept_13_4_7_3_1_92 30 85 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 198 (accept_3_5 29 85 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 198 (Polychromatic418967fa.accept_15_13_10_3_1_1952 28 85 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 198 (accept_3_5 26 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  85 198 (Polychromatic418967fa.accept_23_2_16_14_1_11540 25 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 85 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 85 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 198 (accept_3_5 23 85 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 85 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 198
  (Polychromatic418967fa.accept_13_8_7_3_1_430 21 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 198 (accept_3_5 20 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 198 (Polychromatic418967fa.accept_19_18_9_8_1_3267 18 85 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 198 (accept_3_5 17 85 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 198 (Polychromatic418967fa.accept_19_16_9_8_1_11539 16 85
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 198 (accept_3_5 14 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 85 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 198 (accept_3_5 11 85 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 85 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 198
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 198 (accept_3_5 8 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 85 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 85 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 198 (accept_3_5 5 85 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 85 198 (Polychromatic418967fa.accept_13_4_7_3_1_92 4 85 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 198 (accept_3_5 2 85 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 198 (Polychromatic418967fa.accept_13_1_7_3_1_1503 1
  85 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 198
  (allA_succ_of_accept 83 84 198 (Polychromatic418967fa.accept_13_5_6_3_1_868 83 84 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 84 198 2 41 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 84 198 3 27 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 84 198 2 40 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 79
  84 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 198 6 13 14 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 198
  (Polychromatic418967fa.accept_16_13_4_6_1_2322 77 84 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 84 198 2 38 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 75 84 198 3 25 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 74 84 198 2 37 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 84 198 (Polychromatic418967fa.accept_15_13_9_3_1_1949 73 84 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 198 6 12 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 198 (Polychromatic418967fa.accept_24_23_12_6_1_6187
  71 84 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 198 2 35 42 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 84 198 3 23 28 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 84 198 2 34 42 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 198
  (Polychromatic418967fa.accept_16_3_4_6_1_6798 67 84 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 198 6 11 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 84 198 (Polychromatic418967fa.accept_15_5_9_3_1_528 65 84 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 84 198 2 32 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 84 198 3 21 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 84 198 2 31 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 198 (Polychromatic418967fa.accept_13_9_6_3_1_1514
  61 84 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 198 6 10 14 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 59 84 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 84 198 2 29 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 84 198 3 19 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 84 198 2 28 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 84 198 (Polychromatic418967fa.accept_15_10_9_3_1_1947 55 84 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 198 6 9 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 198 (Polychromatic418967fa.accept_13_1_6_3_1_1547 53 84 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 198 2 26 42 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 84 198 3 17 28 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 84 198 2 25 42 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 84 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 198 6 8 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 84 198 (Polychromatic418967fa.accept_23_1_15_14_1_11538 47 84 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 198 2 23 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 84 198 3 15 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 84 198 2 22 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 198 (Polychromatic418967fa.accept_15_13_9_3_1_1949
  43 84 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 198 6 7 14 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 198
  (Polychromatic418967fa.accept_24_17_12_6_1_6190 41 84 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 84 198 2 20 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 84 198 3 13 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 84 198 2 19 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 84 198 (Polychromatic418967fa.accept_16_5_4_6_1_3349 37 84 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 198 6 6 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 198 (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 84 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 198 2 17 42 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 84 198 3 11 28 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 84 198 2 16 42 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 198
  (Polychromatic418967fa.accept_13_5_6_3_1_868 31 84 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 198 6 5 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 84 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 84 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 198 2 14 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 84 198 3 9 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 84 198 2 13 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 198 (Polychromatic418967fa.accept_15_10_9_3_1_1947
  25 84 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 198 6 4 14 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 198
  (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 84 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 84 198 2 11 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 84 198 3 7 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 84 198 2 10 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 19 84 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 198 6 3 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 198 (Polychromatic418967fa.accept_24_17_12_6_1_6190 17 84
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 198 2 8 42 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 84 198 3 5 28 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 84 198 2 7 42 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 198
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 84 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 198 6 2 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 198 (Polychromatic418967fa.accept_16_11_4_6_1_4422 11 84 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 198 2 5 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 84 198 3 3 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 84 198 2 4 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 198 (Polychromatic418967fa.accept_24_7_12_6_1_6188 7 84 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 198 6 1 14 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 198
  (Polychromatic418967fa.accept_13_5_6_3_1_868 5 84 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 198 2 2 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 84 198 3 1 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 84 198 2 1 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 84 198 (Polychromatic418967fa.accept_13_1_6_3_1_1547 1 84 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 84
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 198
  (allA_succ_of_accept 82 83 198 (accept_3_4 82 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 198 (accept_3_4 79 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 83 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 198 (accept_3_4 76 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165 75 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 198 (accept_3_4 73 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 198 (Polychromatic418967fa.accept_15_12_8_3_1_1995 72 83 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 198 (accept_3_4 70 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 198 (Polychromatic418967fa.accept_16_4_3_6_1_6805 68 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 198 (accept_3_4 67 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 83 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 198 (accept_3_4 64 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 198 (Polychromatic418967fa.accept_13_11_5_3_1_889 63 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 198 (Polychromatic418967fa.accept_20_2_3_18_1_8645 62 83 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 198 (accept_3_4 61 83 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 83 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 198 (accept_3_4 58 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 198 (accept_3_4 55 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 198 (Polychromatic418967fa.accept_13_2_5_3_1_406 54 83 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 198 (accept_3_4 52 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 198 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 198 (accept_3_4 49 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 198 (Polychromatic418967fa.accept_13_9_5_3_1_428 48 83 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 198
  (Polychromatic418967fa.accept_13_8_5_3_1_427 47 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 198 (accept_3_4 46 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 198 (Polychromatic418967fa.accept_19_6_7_8_1_10108 44 83 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 198 (accept_3_4 43 83 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 198 (Polychromatic418967fa.accept_15_12_8_3_1_1995 42 83
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 198 (accept_3_4 40 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 198 (accept_3_4 37 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 83 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 198
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 198 (accept_3_4 34 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 198 (accept_3_4 31 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 198 (Polychromatic418967fa.accept_17_13_15_11_1_2936 30 83 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 198 (accept_3_4 28 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 198 (Polychromatic418967fa.accept_13_1_5_3_1_888 27 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 198 (accept_3_4 25 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 83 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 198
  (Polychromatic418967fa.accept_21_2_20_9_1_2507 23 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 198 (accept_3_4 22 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 198 (Polychromatic418967fa.accept_15_5_8_3_1_556 20 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 198 (accept_3_4 19 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 83 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 198 (accept_3_4 16 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 198 (Polychromatic418967fa.accept_13_1_5_3_1_888 14 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 198 (accept_3_4 13 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 198 (Polychromatic418967fa.accept_15_12_8_3_1_1995 12 83 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 198 (accept_3_4 10 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 83 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 83 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 198 (accept_3_4 7 83 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 83 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 83 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 198 (accept_3_4 4 83 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 83
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 198
  (Polychromatic418967fa.accept_13_2_5_3_1_406 2 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 198 (accept_3_4 1 83 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 198
  (allA_succ_of_accept 81 82 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 82 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 82 198 2 40 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 82 198 (Polychromatic418967fa.accept_13_1_4_3_1_1545
  79 82 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 82 198 2 39 41 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 82 198 (accept_3_5 77
  82 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 82 198 2 38 41 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 82 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 75 82 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 82 198 2 37 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 82 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 73 82 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 82 198 2 36 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 82 198 (accept_3_5 71 82 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 82 198 2 35 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 82 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 69 82 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 82 198 2 34 41 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 82 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 67 82 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 82 198 2 33 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 82 198 (accept_3_5 65 82 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 82
  198 2 32 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  82 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 63 82 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 82 198 2 31 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 82 198 (Polychromatic418967fa.accept_28_5_26_2_1_11537 61 82 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 82 198 2 30 41 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 82 198 (accept_3_5 59 82 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 82 198 2 29 41 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 82 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 57 82 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 82 198 2 28 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 82 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 55 82 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 82 198 2 27 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 82 198 (accept_3_5 53 82 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 82 198 2 26 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 82 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 51 82 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 82 198 2 25 41 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 82 198
  (Polychromatic418967fa.accept_14_7_12_2_1_2502 49 82 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 82 198 2 24 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 82 198 (accept_3_5 47 82 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 82
  198 2 23 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  82 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 82 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 82 198 2 22 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 82 198 (Polychromatic418967fa.accept_16_11_2_6_1_1435 43 82 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 82 198 2 21 41 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 82 198 (accept_3_5 41 82 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 82 198 2 20 41 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 82 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 82 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 82 198 2 19 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 82 198 (Polychromatic418967fa.accept_17_3_14_11_1_5243 37 82 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 82 198 2 18 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 82 198 (accept_3_5 35 82 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82 198 2 17 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 82 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 82 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 82 198 2 16 41 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 82 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 82 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 82 198 2 15 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 82 198 (accept_3_5 29 82 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82
  198 2 14 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  82 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 82 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 82 198 2 13 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 82 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 82 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 82 198 2 12 41 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 82 198 (accept_3_5 23 82 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82 198 2 11 41 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 82 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 21 82 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 82 198 2 10 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 82 198 (Polychromatic418967fa.accept_15_4_7_3_1_119 19 82 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 82 198 2 9 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 198 (accept_3_5 17 82 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 82 198 2 8 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 82 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 82 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 82 198 2 7 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 198 (Polychromatic418967fa.accept_19_13_6_8_1_8741
  13 82 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 198 2 6 41 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 198 (accept_3_5 11
  82 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 198 2 5 41 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 82 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 198 2 4 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 198 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 82 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 198 2 3 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 198 (accept_3_5 5 82 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 198 2 2 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 82 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 198 2 1 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 198 (Polychromatic418967fa.accept_13_1_4_3_1_1545 1
  82 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 198
  (allA_succ_of_accept 80 81 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 80 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 81 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 198 3 26 27 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 198
  (Polychromatic418967fa.accept_20_17_1_18_1_11536 77 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 81 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 76 81 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 198 3 25 27 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 198
  (Polychromatic418967fa.accept_12_2_9_6_1_439 74 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 81 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 73 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 81 198 9 8 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 81 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 81 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 198
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 70 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 81 198 3 23 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 81 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 81 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 198 3 22 27 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 198
  (Polychromatic418967fa.accept_14_9_11_2_1_2501 65 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 81 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 64 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 81 198 9 7 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 81 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 81 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 61 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 81 198 3 20 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 81 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 58 81
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 198 3 19 27 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 198
  (Polychromatic418967fa.accept_12_8_9_6_1_127 56 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 81 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 81 198 9 6 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 81 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 53 81 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 52 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 81 198 3 17 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 81 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 50 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 198 (Polychromatic418967fa.accept_10_9_1_8_1_755 49 81 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 198 3 16 27 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 81 198 9 5 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 81 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 81 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 81 198 3 14 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 81 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 81 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 198 3 13 27 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 198
  (Polychromatic418967fa.accept_12_2_9_6_1_439 38 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 198 (Polychromatic418967fa.accept_14_9_11_2_1_2501 37 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 81 198 9 4 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 81 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 81 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 34 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 81 198 3 11 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 81 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 81 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 198 3 10 27 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 198
  (Polychromatic418967fa.accept_10_9_1_8_1_755 29 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 81 198 9 3 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 81 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 81 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 198
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 81 198 3 8 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 81 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 81
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 198 3 7 27 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 81 198 9 2 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 81 198 (Polychromatic418967fa.accept_20_17_1_18_1_11536 17 81
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 81 198 3 5 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 81 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 81 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 198 3 4 27 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 81 198 9 1 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 81 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 81 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 81 198 3 2 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 81 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 81 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 198 3 1 27 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 198
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 81 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 81 198 (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 81 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 81
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 198
  (allA_succ_of_accept 79 80 198 (accept_3_4 79 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 80
  198 2 39 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77
  80 198 (Polychromatic418967fa.accept_13_12_2_3_1_1527 77 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 80 198 2 38 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 80 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 80 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 80 198 2 37 40 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 80 198 (accept_3_4 73 80 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 80 198 2 36 40 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 80 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 71 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 80 198 2 35 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 80 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 80 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 198 2 34 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 198 (accept_3_4 67 80 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 198 2 33 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 80 198 (Polychromatic418967fa.accept_17_14_12_11_1_4063 65 80
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 80 198 2 32 40 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 80 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 80 198 2 31 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 80 198 (accept_3_4 61 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80
  198 2 30 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  80 198 (Polychromatic418967fa.accept_27_5_26_9_1_11486 59 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 80 198 2 29 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 80 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 80 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 80 198 2 28 40 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 80 198 (accept_3_4 55 80 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80 198 2 27 40 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 80 198
  (Polychromatic418967fa.accept_13_1_2_3_1_911 53 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 80 198 2 26 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 80 198 (Polychromatic418967fa.accept_12_3_8_6_1_895 51 80 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 198 2 25 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 198 (accept_3_4 49 80 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 198 2 24 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 80 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 198 2 23 40 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 80 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 80 198 2 22 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 80 198 (accept_3_4 43 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80
  198 2 21 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  80 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 80 198 2 20 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 80 198 (Polychromatic418967fa.accept_12_3_8_6_1_895 39 80 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 198 2 19 40 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 198 (accept_3_4 37 80 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 198 2 18 40 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 80 198
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 35 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 80 198 2 17 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 80 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 80 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 80 198 2 16 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 80 198 (accept_3_4 31 80 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 198 2 15 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 80 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 80 198 2 14 40 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 80 198
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 80 198 2 13 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 80 198 (accept_3_4 25 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80
  198 2 12 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  80 198 (Polychromatic418967fa.accept_13_10_2_3_1_3025 23 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 80 198 2 11 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 80 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 80 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 198 2 10 40 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 198 (accept_3_4 19 80 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80 198 2 9 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 80 198 (Polychromatic418967fa.accept_15_2_5_3_1_552 17
  80 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 80 198 2 8 40 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 80 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 80 198 2 7 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 80 198 (accept_3_4 13 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80
  198 2 6 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  80 198 (Polychromatic418967fa.accept_13_11_2_3_1_883 11 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 80 198 2 5 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 80 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 80 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 198 2 4 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 198 (accept_3_4 7 80 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 198 2 3 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 80 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 80 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 80 198 2 2 40 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 80 198 2 1 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 80 198 (accept_3_4 1 80 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 198
  (allA_succ_of_accept 78 79 198 (Polychromatic418967fa.accept_21_15_16_9_1_5303 78 79 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 198 (accept_3_5 77 79 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 198 (Polychromatic418967fa.accept_13_11_1_3_1_910 76 79 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 198
  (Polychromatic418967fa.accept_21_12_16_9_1_8497 75 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 79 198 (accept_3_5 74 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  79 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 79 198 (Polychromatic418967fa.accept_13_7_1_3_1_1523 72 79 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 198 (accept_3_5 71 79 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 79 198 (Polychromatic418967fa.accept_13_5_1_3_1_878 70 79 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 79 198 (accept_3_5 68 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  79 198 (Polychromatic418967fa.accept_10_7_9_8_1_1135 67 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 79 198 (Polychromatic418967fa.accept_21_3_16_9_1_8528 66 79 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 198 (accept_3_5 65 79 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 79 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 64 79 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 198
  (Polychromatic418967fa.accept_13_11_1_3_1_910 63 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 79 198 (accept_3_5 62 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  79 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 79 198 (Polychromatic418967fa.accept_14_4_9_2_1_95 60 79 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 198 (accept_3_5 59 79 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 198 (Polychromatic418967fa.accept_13_6_1_3_1_1522 58 79 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 198 (accept_3_5 56 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 198 (Polychromatic418967fa.accept_16_7_15_6_1_1428 55 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 79 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 198 (accept_3_5 53 79 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 198 (Polychromatic418967fa.accept_15_7_4_3_1_1930 52 79 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 198
  (Polychromatic418967fa.accept_10_1_9_8_1_123 51 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 198 (accept_3_5 50 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 198 (Polychromatic418967fa.accept_21_6_16_9_1_5300 48 79 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 198 (accept_3_5 47 79 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 198 (Polychromatic418967fa.accept_13_7_1_3_1_1523 46 79 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 198 (accept_3_5 44 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 198 (Polychromatic418967fa.accept_13_4_1_3_1_3058 43 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 198 (Polychromatic418967fa.accept_19_4_3_8_1_8788 42 79 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 198 (accept_3_5 41 79 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 198 (Polychromatic418967fa.accept_38_2_3_8_1_11535 40 79 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 198
  (Polychromatic418967fa.accept_14_11_9_2_1_6382 39 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 198 (accept_3_5 38 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 198 (Polychromatic418967fa.accept_19_17_3_8_1_5946 36 79 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 198 (accept_3_5 35 79 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 79 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 198 (accept_3_5 32 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 198 (Polychromatic418967fa.accept_10_1_9_8_1_123 31 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 198 (Polychromatic418967fa.accept_13_4_1_3_1_3058 30 79 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 198 (accept_3_5 29 79 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 198 (Polychromatic418967fa.accept_13_2_1_3_1_419 28 79 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 198
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 198 (accept_3_5 26 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 79 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 198 (accept_3_5 23 79 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 198 (Polychromatic418967fa.accept_15_7_4_3_1_1930 22 79 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 198 (accept_3_5 20 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 198 (Polychromatic418967fa.accept_13_6_1_3_1_1522 19 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 198 (Polychromatic418967fa.accept_13_5_1_3_1_878 18 79 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 198 (accept_3_5 17 79 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 198 (Polychromatic418967fa.accept_15_1_4_3_1_1928 16 79 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 198
  (Polychromatic418967fa.accept_13_2_1_3_1_419 15 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 198 (accept_3_5 14 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 198 (Polychromatic418967fa.accept_21_12_16_9_1_8497 12 79 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 198 (accept_3_5 11 79 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 198 (Polychromatic418967fa.accept_21_10_16_9_1_5302 10 79
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 198 (accept_3_5 8 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  198 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 198 (Polychromatic418967fa.accept_13_6_1_3_1_1522 6 79 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 198 (accept_3_5 5 79 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 79 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 198
  (Polychromatic418967fa.accept_21_3_16_9_1_8528 3 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 198 (accept_3_5 2 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 198
  (allA_succ_of_accept 77 78 198 (Polychromatic418967fa.accept_19_1_2_8_1_10129 77 78 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78 198 2 38 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 78 198 3 25 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 78 198 2 37 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 73
  78 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 198 6 12 13 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 198
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 71 78 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 78 198 2 35 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 78 198 3 23 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 78 198 2 34 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 78 198 (Polychromatic418967fa.accept_19_10_2_8_1_3206 67 78 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 198 6 11 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 198 (Polychromatic418967fa.accept_21_2_15_9_1_3838
  65 78 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 198 2 32 39 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 78 198 3 21 26 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 78 198 2 31 39 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 198
  (Polychromatic418967fa.accept_21_19_15_9_1_11533 61 78 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 78 198 6 10 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 78 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 78 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 198 2 29 39 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 78 198 3 19 26 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 78 198 2 28 39 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 78 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 198 6 9 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 78 198 (Polychromatic418967fa.accept_19_15_2_8_1_7263 53 78 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 198 2 26 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 78 198 3 17 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 78 198 2 25 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 198 (Polychromatic418967fa.accept_19_11_2_8_1_8802
  49 78 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 198 6 8 13 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 198
  (Polychromatic418967fa.accept_21_5_15_9_1_11534 47 78 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 78 198 2 23 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 78 198 3 15 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 78 198 2 22 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 78 198 (Polychromatic418967fa.accept_14_1_8_2_1_1675 43 78 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 198 6 7 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 78 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 198 2 20 39 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 78 198 3 13 26 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 78 198 2 19 39 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 198
  (Polychromatic418967fa.accept_17_3_10_11_1_7848 37 78 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 198 6 6 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 78 198 (Polychromatic418967fa.accept_17_1_10_11_1_2943 35 78 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 198 2 17 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 78 198 3 11 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 78 198 2 16 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 31
  78 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 198 6 5 13 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 198
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 29 78 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 78 198 2 14 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 78 198 3 9 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 78 198 2 13 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 78 198 (Polychromatic418967fa.accept_19_6_2_8_1_4496 25 78 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 198 6 4 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 198 (Polychromatic418967fa.accept_21_2_15_9_1_3838 23 78 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 198 2 11 39 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 78 198 3 7 26 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 78 198 2 10 39 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 198
  (Polychromatic418967fa.accept_21_19_15_9_1_11533 19 78 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 78 198 6 3 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 78 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 78 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 198 2 8 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 78 198 3 5 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 78 198 2 7 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 13
  78 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 198 6 2 13 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 198
  (Polychromatic418967fa.accept_19_11_2_8_1_8802 11 78 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 78 198 2 5 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 78 198 3 3 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 78 198 2 4 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 198 (Polychromatic418967fa.accept_21_7_15_9_1_5289 7 78 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 198 6 1 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 198 (Polychromatic418967fa.accept_19_5_2_8_1_8803 5 78 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 198 2 2 39 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 78 198 3 1 26 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 78 198 2 1 39 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 198
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 1 78 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 198
  (allA_succ_of_accept 76 77 198 (accept_3_4 76 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 198 (Polychromatic418967fa.accept_13_9_12_3_1_907 74 77 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 198 (accept_3_4 73 77 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 198 (Polychromatic418967fa.accept_15_12_2_3_1_1146 72 77 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 198 (accept_3_4 70 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 69 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 198 (Polychromatic418967fa.accept_14_12_7_2_1_1663 68 77 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 198 (accept_3_4 67 77 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 77 198 11 6 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 77 198 (Polychromatic418967fa.accept_10_5_7_8_1_1176 65 77 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 77 198 (accept_3_4 64 77 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 77 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 63
  77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 77 198
  (Polychromatic418967fa.accept_20_2_17_18_1_11496 62 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 77 198 (accept_3_4 61 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 77 198 (Polychromatic418967fa.accept_21_18_14_9_1_5351 60 77 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 77 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 77 198 (accept_3_4 58 77 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 77 198 (Polychromatic418967fa.accept_15_12_2_3_1_1146
  57 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 77 198
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 56 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 77 198 11 5 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 77 198 (Polychromatic418967fa.accept_13_2_12_3_1_415 54 77 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 198 (Polychromatic418967fa.accept_17_2_9_11_1_4057 53 77
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 77 198 (accept_3_4 52 77 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 77 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 198
  (Polychromatic418967fa.accept_15_5_2_3_1_4876 50 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 77 198 (accept_3_4 49 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  77 198 (Polychromatic418967fa.accept_13_9_12_3_1_907 48 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 77 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 77 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 198 (accept_3_4 46 77 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 77 198 (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 77 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 77 198 11 4 7 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 77 198 (accept_3_4 43 77 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 198 (Polychromatic418967fa.accept_15_12_2_3_1_1146 42 77
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 198
  (Polychromatic418967fa.accept_13_2_12_3_1_415 41 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 198 (accept_3_4 40 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 198 (Polychromatic418967fa.accept_21_17_14_9_1_8456 38 77 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 198 (accept_3_4 37 77 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 198 (Polychromatic418967fa.accept_16_4_13_6_1_4417 36 77
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 198 (accept_3_4 34 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 77
  198 11 3 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32
  77 198 (Polychromatic418967fa.accept_19_13_1_8_1_3281 32 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 77 198 (accept_3_4 31 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 77 198 (Polychromatic418967fa.accept_13_4_12_3_1_2999 30 77 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 77 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 77 198 (accept_3_4 28 77 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 77 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 198
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 26 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 198 (accept_3_4 25 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 198 (Polychromatic418967fa.accept_21_3_14_9_1_5299 24 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 77 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 77 198 11 2 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 77 198 (Polychromatic418967fa.accept_19_2_1_8_1_7279
  21 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 77 198
  (Polychromatic418967fa.accept_15_5_2_3_1_4876 20 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 198 (accept_3_4 19 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 198 (Polychromatic418967fa.accept_19_18_1_8_1_7291 18 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 198 (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 77 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 198 (accept_3_4 16 77 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 77 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 198
  (Polychromatic418967fa.accept_15_14_2_3_1_1980 14 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 77 198 (accept_3_4 13 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  77 198 (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 11 77 198 11 1 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 77 198 (accept_3_4 10 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 77 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 77 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 198 (Polychromatic418967fa.accept_17_8_9_11_1_3976 8 77 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 198 (accept_3_4 7 77 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 198 (Polychromatic418967fa.accept_21_6_14_9_1_6854
  6 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 198
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 198 (accept_3_4 4 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 198 (Polychromatic418967fa.accept_13_2_12_3_1_415 2 77 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 198 (accept_3_4 1 77 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 198 (allA_succ_of_accept 75 76 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 75 76 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 76 198 2 37 38 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 76 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 73 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 76 198 2 36 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 76 198 (accept_3_5 71 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76
  198 2 35 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  76 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 69 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 76 198 2 34 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 76 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 67 76 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 76 198 2 33 38 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 76 198 (accept_3_5 65 76 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 76 198 2 32 38 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 76 198
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 76 198 2 31 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 76 198 (Polychromatic418967fa.accept_20_1_16_18_1_1677 61 76 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 76 198 2 30 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 76 198 (accept_3_5 59 76 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 76 198 2 29 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 76 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 76 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 76 198 2 28 38 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 76 198
  (Polychromatic418967fa.accept_20_15_16_18_1_5597 55 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 76 198 2 27 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 76 198 (accept_3_5 53 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 76 198 2 26 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 76 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 51 76 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 198 2 25 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 198 (Polychromatic418967fa.accept_13_10_11_3_1_1518
  49 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 76 198 2 24 38 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 76 198 (accept_3_5 47
  76 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76 198 2 23 38 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 76 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 76 198 2 22 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 76 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 76 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 198 2 21 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 198 (accept_3_5 41 76 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 198 2 20 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 76 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 76 198 2 19 38 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 76 198
  (Polychromatic418967fa.accept_21_16_13_9_1_2539 37 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 76 198 2 18 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 76 198 (accept_3_5 35 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76
  198 2 17 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  76 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 76 198 2 16 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 76 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 76 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 76 198 2 15 38 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 76 198 (accept_3_5 29 76 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76 198 2 14 38 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 76 198
  (Polychromatic418967fa.accept_12_3_4_6_1_434 27 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 76 198 2 13 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 76 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 76 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 198 2 12 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 198 (accept_3_5 23 76 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 198 2 11 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 76 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 198 2 10 38 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 198
  (Polychromatic418967fa.accept_15_4_1_3_1_1922 19 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 76 198 2 9 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 76 198 (accept_3_5 17 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76
  198 2 8 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  76 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 76 198 2 7 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 76 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 76 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 198 2 6 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 198 (accept_3_5 11 76 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 198 2 5 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 76 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 76 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 198 2 4 38 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 198
  (Polychromatic418967fa.accept_13_7_11_3_1_1540 7 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 76 198 2 3 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 76 198 (accept_3_5 5 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 198
  2 2 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76
  198 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 76 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 76 198 2 1 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 76 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 76 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 76
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 198 (allA_succ_of_accept
  74 75 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 74 75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 75 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 198 3 24 25 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 198
  (Polychromatic418967fa.accept_13_6_10_3_1_897 71 75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 75 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 70 75 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 75 198 3 23 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 75 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 68
  75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 67 75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 75 198 3 22 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 75 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 75 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 64 75 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 75 198 3 21 25 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 75 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 62 75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 75 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 198 3 20 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 59
  75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 198
  (Polychromatic418967fa.accept_12_10_3_6_1_882 58 75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 198 3 19 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 56 75 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 198 (Polychromatic418967fa.accept_21_13_12_9_1_5323 55 75
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 75 198 3 18 25 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 75 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 198 3 17 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 50
  75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 75 198 3 16 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 75 198 (Polychromatic418967fa.accept_10_7_5_8_1_1167 47 75 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 75 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 198 3 15 25 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 198
  (Polychromatic418967fa.accept_12_8_3_6_1_909 44 75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 198 (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 75 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 198 3 14 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 75
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 198
  (Polychromatic418967fa.accept_12_4_3_6_1_879 40 75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 75 198 3 13 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 75 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 75 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 75 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 198 3 12 25 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 198
  (Polychromatic418967fa.accept_14_7_5_2_1_2473 35 75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 34 75 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 198 3 11 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 198 3 10 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 75 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 75 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 198 3 9 25 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 26 75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 75 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 198 3 8 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 198 (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 75 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 22 75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 75 198 3 7 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 75 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 75 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 198 (Polychromatic418967fa.accept_13_6_10_3_1_897 19 75 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 198 3 6 25 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 75 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 198 3 5 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 75 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 75 198 3 4 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 75 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 75 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 198 3 3 25 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 198
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 198 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 75 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 198 3 2 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 75 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 75 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 75 198 3 1 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 75 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 75 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 198 (allA_succ_of_accept
  73 74 198 (accept_3_4 73 74 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 198 2 36 37 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 198
  (Polychromatic418967fa.accept_13_6_9_3_1_915 71 74 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 198 2 35 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 74 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 74 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 198 2 34 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 198 (accept_3_4 67 74 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 198 2 33 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 198 (Polychromatic418967fa.accept_14_9_4_2_1_983 65 74 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 198 2 32 37 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 74 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 74 198 2 31 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 74 198 (accept_3_4 61 74 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 74
  198 2 30 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  74 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 59 74 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 74 198 2 29 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 74 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 57 74 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 74 198 2 28 37 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 74 198 (accept_3_4 55 74 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 74 198 2 27 37 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 74 198
  (Polychromatic418967fa.accept_19_15_17_8_1_10101 53 74 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 74 198 2 26 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 74 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 51 74 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 74 198 2 25 37 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 74 198 (accept_3_4 49 74 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74 198 2 24 37 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 74 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 74 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 74 198 2 23 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 74 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 45 74 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 74 198 2 22 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 74 198 (accept_3_4 43 74 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74 198 2 21 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 74 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 74 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 198 2 20 37 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 74 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 198 2 19 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 74 198 (accept_3_4 37 74 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74
  198 2 18 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  74 198 (Polychromatic418967fa.accept_19_16_17_8_1_8762 35 74 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 74 198 2 17 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 74 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 74 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 74 198 2 16 37 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 74 198 (accept_3_4 31 74 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74 198 2 15 37 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 74 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 29 74 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 74 198 2 14 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 74 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 74 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 74 198 2 13 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 74 198 (accept_3_4 25 74 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74 198 2 12 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 74 198 (Polychromatic418967fa.accept_14_9_4_2_1_983 23 74 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 198 2 11 37 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 74 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 198 2 10 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 74 198 (accept_3_4 19 74 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74
  198 2 9 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  74 198 (Polychromatic418967fa.accept_15_2_14_3_1_1916 17 74 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 74 198 2 8 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 74 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 15 74 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 198 2 7 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 198 (accept_3_4 13 74 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 198 2 6 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 74 198 (Polychromatic418967fa.accept_15_11_14_3_1_1965 11 74 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 74 198 2 5 37 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 74 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 74 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 74 198 2 4 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 74 198 (accept_3_4 7 74 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 198
  2 3 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 74
  198 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 74 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 74 198 2 2 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 74 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 74 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 198 2 1 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 198 (accept_3_4 1 74 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73
  198 (allA_succ_of_accept 72 73 198 (Polychromatic418967fa.accept_13_7_8_3_1_1533 72 73 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 73 198 (accept_3_5 71 73 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 73 198 (Polychromatic418967fa.accept_13_5_8_3_1_1535 70 73 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 198
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 73 198 (accept_3_5 68 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  73 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 73 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 66 73 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 73 198 (accept_3_5 65 73 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 73 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 64 73 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 73 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 73 198 (accept_3_5 62 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  73 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 73 198 (Polychromatic418967fa.accept_21_18_10_9_1_5297 60 73 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 73 198 (accept_3_5 59 73 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 73 198 (Polychromatic418967fa.accept_17_7_5_11_1_2922 58 73
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 73 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 73 198 (accept_3_5 56 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  73 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 73 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 73 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 73 198 (accept_3_5 53 73 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 73 198 (Polychromatic418967fa.accept_43_9_30_26_1_11532 52 73 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 73 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 73 198 (accept_3_5 50 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  73 198 (Polychromatic418967fa.accept_17_15_5_11_1_6468 49 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 73 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 73 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 73 198 (accept_3_5 47 73 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 73 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 46 73 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 73 198
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 73 198 (accept_3_5 44 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  73 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 73 198 (Polychromatic418967fa.accept_15_12_13_3_1_1915 42 73 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 73 198 (accept_3_5 41 73 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 73 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 73 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 73 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 73 198 (accept_3_5 38 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  73 198 (Polychromatic418967fa.accept_13_11_8_3_1_3016 37 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 73 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 73 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 73 198 (accept_3_5 35 73 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 73 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 73 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 73 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 73 198 (accept_3_5 32 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  73 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 73 198 (Polychromatic418967fa.accept_19_11_16_8_1_2098 30 73 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 73 198 (accept_3_5 29 73 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 73 198 (Polychromatic418967fa.accept_19_9_16_8_1_2097 28 73
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 73 198 (accept_3_5 26 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  73 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 73 198 (Polychromatic418967fa.accept_13_11_8_3_1_3016 24 73 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 73 198 (accept_3_5 23 73 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 73 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 73 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 73 198
  (Polychromatic418967fa.accept_10_1_3_8_1_136 21 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 73 198 (accept_3_5 20 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  73 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 73 198 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 73 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 198 (accept_3_5 17 73 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 73 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 73 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 73 198 (accept_3_5 14 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  73 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 73 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 73 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 198 (accept_3_5 11 73 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 198 (Polychromatic418967fa.accept_15_10_13_3_1_4816 10 73 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 198
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 198 (accept_3_5 8 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73
  198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 73 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 198 (accept_3_5 5 73 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 198 (Polychromatic418967fa.accept_27_4_19_9_1_9633 4 73 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 198 (accept_3_5 2 73 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 73
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 198 (allA_succ_of_accept 71
  72 198 (Polychromatic418967fa.accept_23_2_3_14_1_11509 71 72 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 72 198 2 35 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 69 72 198 3 23 24 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 72 198 2 34 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 72 198 (Polychromatic418967fa.accept_15_7_12_3_1_1137 67 72 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 198 6 11 12 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 65 72 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 72 198 2 32 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 72 198 9 7 8 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 72 198 2 31 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 72 198 (Polychromatic418967fa.accept_13_9_7_3_1_1531 61 72 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 198 6 10 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 198 (Polychromatic418967fa.accept_19_2_15_8_1_7306
  59 72 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 198 2 29 36 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 72 198 3 19 24 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 72 198 2 28 36 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 55 72 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 198 18 3 4 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 198 (Polychromatic418967fa.accept_13_1_7_3_1_1503 53 72 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 198 2 26 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 72 198 3 17 24 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 72 198 2 25 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 198 (Polychromatic418967fa.accept_13_10_7_3_1_3041
  49 72 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 198 6 8 12 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 198
  (Polychromatic418967fa.accept_13_8_7_3_1_430 47 72 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 72 198 2 23 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 72 198 9 5 8 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 72 198 2 22 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 198 (Polychromatic418967fa.accept_13_4_7_3_1_92 43 72 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 198 6 7 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 198 (Polychromatic418967fa.accept_19_3_15_8_1_3232 41 72 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72 198 2 20 36 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 72 198 3 13 24 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 72 198 2 19 36 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 198
  (Polychromatic418967fa.accept_13_11_7_3_1_894 37 72 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 198 18 2 4 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 72 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 198 2 17 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 72 198 3 11 24 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 72 198 2 16 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 198
  (Polychromatic418967fa.accept_19_12_15_8_1_10070 31 72 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 72 198 6 5 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 72 198 (Polychromatic418967fa.accept_26_3_20_16_1_9717 29 72 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 198 2 14 36 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 72 198 9 3 8 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 72 198 2 13 36 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 72 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 198 6 4 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 198 (Polychromatic418967fa.accept_13_10_7_3_1_3041 23 72 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 198 2 11 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 72 198 3 7 24 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 72 198 2 10 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 198
  (Polychromatic418967fa.accept_25_19_22_23_1_11531 19 72 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 72 198 18 1 4 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 72 198 (Polychromatic418967fa.accept_13_4_7_3_1_92 17 72 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 198 2 8 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 72 198 3 5 24 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 72 198 2 7 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 198 (Polychromatic418967fa.accept_15_13_12_3_1_1180
  13 72 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 198 6 2 12 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 198
  (Polychromatic418967fa.accept_13_11_7_3_1_894 11 72 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 72 198 2 5 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 72 198 9 1 8 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 72 198 2 4 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 198 (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 72 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 198 6 1 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 72 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 198 2 2 36 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 72 198 3 1 24 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 72 198 2 1 36 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 198
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 1 72 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 198
  (allA_succ_of_accept 70 71 198 (accept_3_4 70 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 198 (Polychromatic418967fa.accept_15_8_11_3_1_3847 68 71 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 198 (accept_3_4 67 71 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 71 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 198 (accept_3_4 64 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 63 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 71 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 198 (accept_3_4 61 71 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 198 (Polychromatic418967fa.accept_17_9_3_11_1_3983 60 71 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 198 (accept_3_4 58 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 198 (Polychromatic418967fa.accept_20_16_11_18_1_11530 56 71 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 198 (accept_3_4 55 71 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 198 (Polychromatic418967fa.accept_21_12_8_9_1_8447 54 71
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 198 (accept_3_4 52 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 198 (Polychromatic418967fa.accept_15_6_11_3_1_1172 51 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 198 (Polychromatic418967fa.accept_14_8_1_2_1_965 50 71 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 198 (accept_3_4 49 71 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 71 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 198
  (Polychromatic418967fa.accept_16_15_7_6_1_1453 47 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 198 (accept_3_4 46 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 198 (Polychromatic418967fa.accept_13_5_6_3_1_868 44 71 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 198 (accept_3_4 43 71 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 198 (Polychromatic418967fa.accept_19_4_14_8_1_4510 42 71 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 198 (accept_3_4 40 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 198 (Polychromatic418967fa.accept_10_9_1_8_1_755 39 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 71 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 198 (accept_3_4 37 71 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 198 (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 71 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 198
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 198 (accept_3_4 34 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 198 (Polychromatic418967fa.accept_19_13_14_8_1_4490 32 71 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 198 (accept_3_4 31 71 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 198 (Polychromatic418967fa.accept_25_5_21_23_1_11529 30 71
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 198 (accept_3_4 28 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 198 (Polychromatic418967fa.accept_17_9_3_11_1_3983 26 71 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 198 (accept_3_4 25 71 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 71 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 198
  (Polychromatic418967fa.accept_10_3_1_8_1_132 23 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 198 (accept_3_4 22 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 71 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 198 (accept_3_4 19 71 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 198 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 71 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 198 (accept_3_4 16 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 198 (Polychromatic418967fa.accept_16_15_7_6_1_1453 15 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 198 (Polychromatic418967fa.accept_13_1_6_3_1_1547 14 71 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 198 (accept_3_4 13 71 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 198 (Polychromatic418967fa.accept_21_12_8_9_1_8447 12 71 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 198
  (Polychromatic418967fa.accept_23_11_2_14_1_11528 11 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 71 198 (accept_3_4 10 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 71 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 198 (Polychromatic418967fa.accept_14_8_1_2_1_965 8 71 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 198 (accept_3_4 7 71 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 198 (accept_3_4 4 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  198 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 71 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 198 (Polychromatic418967fa.accept_17_2_3_11_1_2919 2 71 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 198 (accept_3_4 1 71 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 198
  (allA_succ_of_accept 69 70 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 69 70 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 70 198 2 34 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 70 198 (Polychromatic418967fa.accept_13_2_5_3_1_406 67
  70 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 198 2 33 35 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 70 198 (accept_3_5 65
  70 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 70 198 2 32 35 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 70 198
  (Polychromatic418967fa.accept_12_3_10_6_1_442 63 70 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 70 198 2 31 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 70 198 (Polychromatic418967fa.accept_13_9_5_3_1_428 61 70 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 198 2 30 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 198 (accept_3_5 59 70 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70 198 2 29 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 70 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 57 70 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 70 198 2 28 35 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 70 198
  (Polychromatic418967fa.accept_20_15_10_18_1_8658 55 70 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 70 198 2 27 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 70 198 (accept_3_5 53 70 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 70 198 2 26 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 70 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 51 70 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 198 2 25 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 70 198 (Polychromatic418967fa.accept_24_1_22_6_1_11505
  49 70 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 70 198 2 24 35 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 198 (accept_3_5 47
  70 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 198 2 23 35 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 70 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 45 70 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 70 198 2 22 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 70 198 (Polychromatic418967fa.accept_15_13_10_3_1_1952 43 70 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 198 2 21 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 198 (accept_3_5 41 70 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70 198 2 20 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 70 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 70 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 70 198 2 19 35 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 70 198
  (Polychromatic418967fa.accept_13_11_5_3_1_889 37 70 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 70 198 2 18 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 70 198 (accept_3_5 35 70 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 70
  198 2 17 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  70 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 70 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 70 198 2 16 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 70 198 (Polychromatic418967fa.accept_21_10_7_9_1_11527 31 70 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 198 2 15 35 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 198 (accept_3_5 29 70 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 198 2 14 35 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 198
  (Polychromatic418967fa.accept_12_3_10_6_1_442 27 70 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 70 198 2 13 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 70 198 (Polychromatic418967fa.accept_17_8_2_11_1_4069 25 70 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 70 198 2 12 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 198 (accept_3_5 23 70 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 198 2 11 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 70 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 70 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 70 198 2 10 35 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 198
  (Polychromatic418967fa.accept_13_6_5_3_1_426 19 70 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 70 198 2 9 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 70 198 (accept_3_5 17 70 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70
  198 2 8 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  70 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 70 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 70 198 2 7 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 70 198 (Polychromatic418967fa.accept_15_13_10_3_1_1952 13 70 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 198 2 6 35 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 198 (accept_3_5 11 70 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 198 2 5 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 70 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 70 198 2 4 35 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 70 198
  (Polychromatic418967fa.accept_15_7_10_3_1_2891 7 70 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 70 198 2 3 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 70 198 (accept_3_5 5 70 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 198
  2 2 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 70
  198 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 70 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 70 198 2 1 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 70 198 (Polychromatic418967fa.accept_13_1_5_3_1_888 1 70 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 198 (allA_succ_of_accept 68 69
  198 (Polychromatic418967fa.accept_12_8_9_6_1_127 68 69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 69 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 69 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 198 3 22 23 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 198
  (Polychromatic418967fa.accept_15_5_9_3_1_528 65 69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 69 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 69 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 69 198 3 21 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 69 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 62
  69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 198
  (Polychromatic418967fa.accept_10_1_9_8_1_123 61 69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 69 198 3 20 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 69 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 69 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 58 69
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 198 3 19 23 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 198
  (Polychromatic418967fa.accept_12_8_9_6_1_127 56 69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 69 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 198 3 18 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 53
  69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 52 69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 69 198 3 17 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 69 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 69 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 198 (Polychromatic418967fa.accept_16_1_5_6_1_4435 49 69 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 198 3 16 23 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 69 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 198 3 15 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 44
  69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 69 198 3 14 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 69 198 (Polychromatic418967fa.accept_10_1_9_8_1_123 41 69 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 69 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 198 3 13 23 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 198 (Polychromatic418967fa.accept_10_7_9_8_1_1135 37 69 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 198 3 12 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 198
  (Polychromatic418967fa.accept_10_4_9_8_1_125 34 69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 69 198 3 11 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 69 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 69 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 69 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 198 3 10 23 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 69 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 198 3 9 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 69 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 198 3 8 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 69 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 69 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 69 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 198 3 7 23 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 198
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 198 3 6 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 69 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 198 3 5 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 69 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 198 (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 69
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 198 3 4 23 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 69 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 198 3 3 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 69 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 198 3 2 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 198 (Polychromatic418967fa.accept_15_5_9_3_1_528 5 69 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 69 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 198 3 1 23 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 198
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 69 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 69 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 68 198 (allA_succ_of_accept 67 68 198 (accept_3_4 67 68 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 68 198 2 33 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 68 198 (Polychromatic418967fa.accept_15_5_8_3_1_556 65 68 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 68 198 2 32 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 68 198 (Polychromatic418967fa.accept_12_3_8_6_1_895 63
  68 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 198 2 31 34 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 198 (accept_3_4 61
  68 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 198 2 30 34 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 68 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 68 198 2 29 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 68 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 57 68 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 68 198 2 28 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 68 198 (accept_3_4 55 68 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68 198 2 27 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 68 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 68 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 68 198 2 26 34 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 68 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 51 68 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 68 198 2 25 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 68 198 (accept_3_4 49 68 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68
  198 2 24 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  68 198 (Polychromatic418967fa.accept_19_9_11_8_1_10050 47 68 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 68 198 2 23 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 68 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 68 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 198 2 22 34 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 198 (accept_3_4 43 68 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 198 2 21 34 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 198
  (Polychromatic418967fa.accept_15_11_8_3_1_1943 41 68 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 68 198 2 20 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 68 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 68 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 198 2 19 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 198 (accept_3_4 37 68 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 198 2 18 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 68 198 (Polychromatic418967fa.accept_14_7_12_2_1_2502 35 68 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 198 2 17 34 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 68 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 198 2 16 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 68 198 (accept_3_4 31 68 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68
  198 2 15 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  68 198 (Polychromatic418967fa.accept_16_13_4_6_1_2322 29 68 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 68 198 2 14 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 68 198 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 68 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 198 2 13 34 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 198 (accept_3_4 25 68 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 198 2 12 34 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 198
  (Polychromatic418967fa.accept_20_3_8_18_1_5603 23 68 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 68 198 2 11 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 68 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 68 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 198 2 10 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 198 (accept_3_4 19 68 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68 198 2 9 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 68 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 68 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 198 2 8 34 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 68 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 68 198 2 7 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 68 198 (accept_3_4 13 68 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68
  198 2 6 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  68 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 68 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 68 198 2 5 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 68 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 68 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 198 2 4 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 198 (accept_3_4 7 68 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 198 2 3 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 68 198 (Polychromatic418967fa.accept_15_5_8_3_1_556 5 68 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 198 2 2 34 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 68 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 68 198 2 1 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 68 198 (accept_3_4 1 68 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 198 (allA_succ_of_accept 66 67
  198 (Polychromatic418967fa.accept_13_1_2_3_1_911 66 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 67 198 (accept_3_5 65 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 67 198 (Polychromatic418967fa.accept_13_12_2_3_1_1527 64 67 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 67 198 (Polychromatic418967fa.accept_13_11_2_3_1_883 63 67 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 198 (accept_3_5 62 67 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 61
  67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 198
  (Polychromatic418967fa.accept_21_18_4_9_1_8484 60 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 198 (accept_3_5 59 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 198 (Polychromatic418967fa.accept_21_16_4_9_1_11526 58 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 67 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 198 (accept_3_5 56 67 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 67 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 198 (accept_3_5 53 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 198 (Polychromatic418967fa.accept_16_4_3_6_1_6805 52 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 198 (Polychromatic418967fa.accept_13_12_2_3_1_1527 51 67 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 198 (accept_3_5 50 67 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 67 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 198 (accept_3_5 47 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 198 (Polychromatic418967fa.accept_17_12_16_11_1_7885 46 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 67 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 198 (accept_3_5 44 67 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 198 (Polychromatic418967fa.accept_16_11_3_6_1_4462 43 67 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 198
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 42 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 198 (accept_3_5 41 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 67 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 198 (accept_3_5 38 67 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 67 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 198
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 198 (accept_3_5 35 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 67 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 198 (accept_3_5 32 67 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 198 (Polychromatic418967fa.accept_13_5_2_3_1_1526 31 67 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 198
  (Polychromatic418967fa.accept_19_11_10_8_1_7256 30 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 198 (accept_3_5 29 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 198 (Polychromatic418967fa.accept_27_1_13_9_1_11525 28 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 67 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 198 (accept_3_5 26 67 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 67 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 198
  (Polychromatic418967fa.accept_13_11_2_3_1_883 24 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 198 (accept_3_5 23 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 198 (Polychromatic418967fa.accept_13_9_2_3_1_3027 22 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 198 (accept_3_5 20 67 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 67 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 198
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 198 (accept_3_5 17 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 198 (Polychromatic418967fa.accept_19_16_10_8_1_10067 16 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 198 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 67 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 198 (accept_3_5 14 67 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 198 (accept_3_5 11 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 198 (Polychromatic418967fa.accept_13_10_2_3_1_3025 10 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 198 (accept_3_5 8 67 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 198 (Polychromatic418967fa.accept_23_7_21_14_1_11524 7 67 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 198 (accept_3_5 5 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  198 (Polychromatic418967fa.accept_15_4_7_3_1_119 4 67 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 198 (Polychromatic418967fa.accept_26_3_15_16_1_5758 3 67 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 198 (accept_3_5 2 67 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 198 (allA_succ_of_accept 65 66
  198 (Polychromatic418967fa.accept_15_5_6_3_1_525 65 66 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 66 198 2 32 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 63 66 198 3 21 22 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 66 198 2 31 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 66 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 66 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 198 6 10 11 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 198
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 59 66 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 66 198 2 29 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 66 198 3 19 22 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 66 198 2 28 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 66 198 11 5 6 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 66 198 6 9 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 66 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 66 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 198 2 26 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 66 198 3 17 22 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 66 198 2 25 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 198 (Polychromatic418967fa.accept_16_1_2_6_1_2295
  49 66 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 198 6 8 11 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 66 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 198 2 23 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 66 198 3 15 22 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 66 198 22 2 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 66 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 198 6 7 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 66 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 198 2 20 33 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 66 198 3 13 22 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 66 198 2 19 33 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 198
  (Polychromatic418967fa.accept_13_11_1_3_1_910 37 66 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 198 6 6 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 198 (Polychromatic418967fa.accept_15_5_6_3_1_525 35 66 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 198 2 17 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 66 198 33 1 2 6 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 66 198 2 16 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 198 (Polychromatic418967fa.accept_13_5_1_3_1_878 31
  66 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 198 6 5 11 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 66 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 198 2 14 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 66 198 3 9 22 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 66 198 2 13 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 66 198 (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 66 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 198 6 4 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 66 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 198 22 1 3 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 66 198 3 7 22 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 66 198 2 10 33 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 66 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 198 6 3 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 198 (Polychromatic418967fa.accept_13_4_1_3_1_3058 17 66 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 198 2 8 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 66 198 3 5 22 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 66 198 2 7 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 66 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 198 6 2 11 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 66 198 11 1 6 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 66 198 2 5 33 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 66 198 3 3 22 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 66 198 2 4 33 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 198
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 66 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 198 6 1 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 66 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 198 2 2 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 66 198 3 1 22 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 66 198 2 1 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 66 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 198 (allA_succ_of_accept 64 65 198
  (accept_3_4 64 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 65 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 198 (accept_3_4 61 65 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 198 (Polychromatic418967fa.accept_14_4_9_2_1_95 60 65 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 59
  65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 198 (accept_3_4 58 65
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 198
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 57 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 65 198 (Polychromatic418967fa.accept_20_16_5_18_1_2846 56 65 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 198 (accept_3_4 55 65 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 65 198 (Polychromatic418967fa.accept_15_9_5_3_1_554 54 65 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 198 (Polychromatic418967fa.accept_10_3_5_8_1_1132
  53 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 198 (accept_3_4 52
  65 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 65 198 (Polychromatic418967fa.accept_16_2_1_6_1_2342 50 65 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 198 (accept_3_4 49 65 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 65 198 (Polychromatic418967fa.accept_21_6_2_9_1_5292 48 65 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 198 (accept_3_4 46 65
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 198
  (Polychromatic418967fa.accept_21_3_2_9_1_5338 45 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 65 198 (Polychromatic418967fa.accept_23_21_19_14_1_11523 44 65 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 198 (accept_3_4 43 65 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 65 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 198
  (Polychromatic418967fa.accept_21_20_2_9_1_5337 41 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 198 (accept_3_4 40 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 198 (Polychromatic418967fa.accept_15_8_5_3_1_1990 38 65 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 198 (accept_3_4 37 65 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 198 (Polychromatic418967fa.accept_15_6_5_3_1_1988 36 65 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 198 (accept_3_4 34 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 198 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 65 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 198 (accept_3_4 31 65 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 198 (Polychromatic418967fa.accept_20_10_5_18_1_5627 30 65 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 198
  (Polychromatic418967fa.accept_17_12_14_11_1_998 29 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 198 (accept_3_4 28 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 198 (Polychromatic418967fa.accept_25_1_15_23_1_11522 26 65 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 198 (accept_3_4 25 65 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 198 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 65 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 198 (accept_3_4 22 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 198 (Polychromatic418967fa.accept_14_7_9_2_1_2489 21 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 198 (Polychromatic418967fa.accept_17_3_14_11_1_5243 20 65 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 198 (accept_3_4 19 65 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 198 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 65 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 198
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 198 (accept_3_4 16 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 198 (Polychromatic418967fa.accept_21_14_2_9_1_6864 14 65 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 198 (accept_3_4 13 65 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 65 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 198 (accept_3_4 10 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 198 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 198 (Polychromatic418967fa.accept_15_8_5_3_1_1990 8 65 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 198 (accept_3_4 7 65 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 198 (Polychromatic418967fa.accept_15_6_5_3_1_1988 6 65 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 198
  (Polychromatic418967fa.accept_16_5_1_6_1_3367 5 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 198 (accept_3_4 4 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 65 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 65 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 198 (accept_3_4 1 65 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 198
  (allA_succ_of_accept 63 64 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 64 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 64 198 2 31 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 64 198 (Polychromatic418967fa.accept_13_9_12_3_1_907
  61 64 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 198 2 30 32 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 198 (accept_3_5 59
  64 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 198 2 29 32 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 198
  (Polychromatic418967fa.accept_12_9_4_6_1_460 57 64 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 64 198 2 28 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 64 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 64 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 64 198 2 27 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 64 198 (accept_3_5 53 64 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64 198 2 26 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 64 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 51 64 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 198 2 25 32 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 64 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 198 2 24 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 64 198 (accept_3_5 47 64 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64
  198 2 23 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  64 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 64 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 64 198 2 22 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 64 198 (Polychromatic418967fa.accept_13_4_12_3_1_2999 43 64 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 198 2 21 32 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 198 (accept_3_5 41 64 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 198 2 20 32 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 64 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 64 198 2 19 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 64 198 (Polychromatic418967fa.accept_15_7_4_3_1_1930 37 64 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 64 198 2 18 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 64 198 (accept_3_5 35 64 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64 198 2 17 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 64 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 64 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 198 2 16 32 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 64 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 198 2 15 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 64 198 (accept_3_5 29 64 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64
  198 2 14 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  64 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 64 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 64 198 2 13 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 64 198 (Polychromatic418967fa.accept_19_6_7_8_1_10108 25 64 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 198 2 12 32 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 198 (accept_3_5 23 64 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 198 2 11 32 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 198
  (Polychromatic418967fa.accept_12_9_4_6_1_460 21 64 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 64 198 2 10 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 64 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 19 64 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 198 2 9 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 198 (accept_3_5 17 64 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 64 198 2 8 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 64 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 64 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 198 2 7 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 13
  64 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 198 2 6 32 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 198 (accept_3_5 11
  64 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 198 2 5 32 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 64 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 64 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 64 198 2 4 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 64 198 (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 64 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 198 2 3 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 198 (accept_3_5 5 64 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 64 198 2 2 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 64 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 64 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 198 2 1 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 198 (Polychromatic418967fa.accept_14_1_8_2_1_1675 1
  64 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 198 (allA_succ_of_accept 62 63 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 62 63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 63 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 198 3 20 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 198 (Polychromatic418967fa.accept_13_7_11_3_1_1540
  59 63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 198
  (Polychromatic418967fa.accept_12_10_3_6_1_882 58 63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 63 198 3 19 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 63 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 63 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165 55 63 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 198 9 6 7 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 52 63 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 198 3 17 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 50
  63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 63 198 3 16 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 63 198 (Polychromatic418967fa.accept_13_8_11_3_1_3053 47 63 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 46 63 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 198 9 5 7 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 198
  (Polychromatic418967fa.accept_12_8_3_6_1_909 44 63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 198 (Polychromatic418967fa.accept_23_20_17_14_1_11521 43 63 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 198 3 14 21 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 40 63 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 198 3 13 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 38
  63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 63 198 9 4 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 63 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 63 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 34 63 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 198 3 11 21 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 198
  (Polychromatic418967fa.accept_12_8_3_6_1_909 32 63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 198 (Polychromatic418967fa.accept_10_1_3_8_1_136 31 63 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 198 3 10 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 63
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 198
  (Polychromatic418967fa.accept_12_4_3_6_1_879 28 63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 63 198 9 3 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 63 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 63 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 198 3 8 21 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 198
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 23 63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 63 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 198 3 7 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 63 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 198
  (Polychromatic418967fa.accept_14_5_7_2_1_468 19 63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 63 198 9 2 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 63 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 63 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 198 3 5 21 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 198 3 4 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 198 (Polychromatic418967fa.accept_10_1_3_8_1_136 11 63 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 198
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 63 198 9 1 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 63 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 63 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 198 (Polychromatic418967fa.accept_13_7_11_3_1_1540 7 63 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 198 3 2 21 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 63 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 198 3 1 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 63 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 198 (allA_succ_of_accept
  61 62 198 (accept_3_4 61 62 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 198 2 30 31 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 62 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 198 2 29 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 62 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 62 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 198 2 28 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 198 (accept_3_4 55 62 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 198 2 27 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 62 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 198 2 26 31 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 51 62 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 198 2 25 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 62 198 (accept_3_4 49 62 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62
  198 2 24 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  62 198 (Polychromatic418967fa.accept_20_7_2_18_1_5618 47 62 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 62 198 2 23 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 62 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 62 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 62 198 2 22 31 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 62 198 (accept_3_4 43 62 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62 198 2 21 31 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 198
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 41 62 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 62 198 2 20 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 62 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 62 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 198 2 19 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 198 (accept_3_4 37 62 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 198 2 18 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 62 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 198 2 17 31 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 62 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 198 2 16 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 62 198 (accept_3_4 31 62 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62
  198 2 15 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  62 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 62 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 62 198 2 14 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 62 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 62 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 198 2 13 31 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 198 (accept_3_4 25 62 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 198 2 12 31 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 198
  (Polychromatic418967fa.accept_19_4_5_8_1_11520 23 62 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 198 2 11 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 62 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 198 2 10 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 198 (accept_3_4 19 62 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 198 2 9 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 62 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 62 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 198 2 8 31 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 62 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 198 2 7 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 198 (accept_3_4 13 62 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  198 2 6 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 62 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 198 2 5 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 62 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 198 2 4 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 198 (accept_3_4 7 62 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 198 2 3 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 62 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 198 2 2 31 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 62 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 198 2 1 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 198 (accept_3_4 1 62 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 198 (allA_succ_of_accept 60 61 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 198 (accept_3_5 59 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 198 (Polychromatic418967fa.accept_13_6_9_3_1_915 58 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 198 (Polychromatic418967fa.accept_13_5_9_3_1_870 57 61 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 198 (accept_3_5 56 61 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 61 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 198
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 54 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 198 (accept_3_5 53 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 61 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 198 (accept_3_5 50 61 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 198 (Polychromatic418967fa.accept_10_9_1_8_1_755 49 61 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 198
  (Polychromatic418967fa.accept_19_10_4_8_1_11500 48 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 198 (accept_3_5 47 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 61 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 198 (accept_3_5 44 61 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 61 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 198
  (Polychromatic418967fa.accept_23_19_15_14_1_9884 42 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 61 198 (accept_3_5 41 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 61 198 (Polychromatic418967fa.accept_24_16_13_6_1_11519 40 61 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 61 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 61 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 198 (accept_3_5 38 61 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 198
  (Polychromatic418967fa.accept_17_3_10_11_1_7848 37 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 61 198 (Polychromatic418967fa.accept_15_6_1_3_1_2852 36 61 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 61 198 (accept_3_5 35 61 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 61 198 (Polychromatic418967fa.accept_13_8_9_3_1_2213 34 61 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 61 198 (Polychromatic418967fa.accept_10_3_1_8_1_132
  33 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 198 (accept_3_5 32
  61 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 61 198 (Polychromatic418967fa.accept_25_5_11_23_1_11518 30 61 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 61 198 (accept_3_5 29 61 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 61 198 (Polychromatic418967fa.accept_13_2_9_3_1_2212 28 61 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 61 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 198 (accept_3_5 26 61
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 61 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 61 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 61 198 (accept_3_5 23 61 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 61 198 (Polychromatic418967fa.accept_19_3_4_8_1_8808 22 61 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 61 198 (Polychromatic418967fa.accept_13_8_9_3_1_2213
  21 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 198 (accept_3_5 20
  61 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 61 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 61 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 198 (accept_3_5 17 61 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 61 198 (Polychromatic418967fa.accept_20_16_1_18_1_5617 16 61 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 61 198 (accept_3_5 14 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  61 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 61 198 (Polychromatic418967fa.accept_13_12_9_3_1_3047 12 61 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 61 198 (accept_3_5 11 61 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 61 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 61 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 198
  (Polychromatic418967fa.accept_10_9_1_8_1_755 9 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 61 198 (accept_3_5 8 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61
  198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 61 198 (Polychromatic418967fa.accept_13_6_9_3_1_915 6 61 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 198 (accept_3_5 5 61 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 61 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 61 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 198 (accept_3_5 2 61 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 198 (Polychromatic418967fa.accept_17_1_10_11_1_2943
  1 61 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 198 (allA_succ_of_accept 59 60 198
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 59 60 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 198 2 29 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 60 198 3 19 20 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 60 198 2 28 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 60 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 60 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 198 6 9 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 198 (Polychromatic418967fa.accept_17_2_9_11_1_4057 53 60 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 198 2 26 30 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 60 198 3 17 20 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 60 198 2 25 30 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 198
  (Polychromatic418967fa.accept_19_11_3_8_1_11517 49 60 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 198 6 8 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 60 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 198 2 23 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 198 3 15 20 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 198 2 22 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 198 (Polychromatic418967fa.accept_19_5_3_8_1_7302
  43 60 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 198 6 7 10 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 60 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 198 2 20 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 60 198 3 13 20 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 60 198 2 19 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 60 198 (Polychromatic418967fa.accept_13_11_8_3_1_3016 37 60 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 198 6 6 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 198 (Polychromatic418967fa.accept_13_9_8_3_1_3045 35 60 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 198 2 17 30 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 60 198 3 11 20 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 60 198 2 16 30 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 198
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 31 60 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 198 6 5 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 198 (Polychromatic418967fa.accept_21_8_18_9_1_5329 29 60 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 198 2 14 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 60 198 3 9 20 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 60 198 2 13 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 198 (Polychromatic418967fa.accept_17_8_9_11_1_3976
  25 60 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 198 6 4 10 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 198
  (Polychromatic418967fa.accept_14_9_4_2_1_983 23 60 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 60 198 2 11 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 60 198 3 7 20 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 60 198 2 10 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 60 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 198 6 3 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 198 (Polychromatic418967fa.accept_19_17_3_8_1_5946 17 60 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 198 2 8 30 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60 198 3 5 20 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60 198 2 7 30 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 60 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 198 6 2 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 198 (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 60 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 198 2 5 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 60 198 3 3 20 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 60 198 2 4 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 198 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 60 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 198 6 1 10 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 60 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 60 198 2 2 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 60 198 3 1 20 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 60 198 2 1 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 198 (Polychromatic418967fa.accept_21_1_18_9_1_5290 1 60 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 198 (allA_succ_of_accept 58 59 198 (accept_3_4 58 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 59 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 59 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 59 198 (Polychromatic418967fa.accept_13_4_7_3_1_92 56 59 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 198 (accept_3_4 55 59 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 54
  59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 198 (accept_3_4 52 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 198 (Polychromatic418967fa.accept_10_1_9_8_1_123 51 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 59 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 198 (accept_3_4 49 59 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 59 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 198 (accept_3_4 46 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 44 59 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 198 (accept_3_4 43 59 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 198 (Polychromatic418967fa.accept_24_18_11_6_1_8079 42 59 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 198 (accept_3_4 40 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 198 (Polychromatic418967fa.accept_19_1_2_8_1_10129 39 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 198 (Polychromatic418967fa.accept_25_13_9_23_1_11494 38 59 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 198 (accept_3_4 37 59 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 59 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 198
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 35 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 198 (accept_3_4 34 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 198 (Polychromatic418967fa.accept_15_2_14_3_1_1916 32 59 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 198 (accept_3_4 31 59 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 198 (Polychromatic418967fa.accept_13_4_7_3_1_92 30 59 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 198 (accept_3_4 28 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 59 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 198 (accept_3_4 25 59 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 59 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 198
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 23 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 198 (accept_3_4 22 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 59 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 198 (accept_3_4 19 59 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 198 (Polychromatic418967fa.accept_16_2_11_6_1_737 18 59 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 198 (accept_3_4 16 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 59 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 198 (accept_3_4 13 59 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 59 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 198
  (Polychromatic418967fa.accept_10_1_9_8_1_123 11 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 198 (accept_3_4 10 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 59 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 198 (accept_3_4 7 59 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 59 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 198 (accept_3_4 4 59 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 198 (Polychromatic418967fa.accept_16_3_11_6_1_4467
  3 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 198
  (Polychromatic418967fa.accept_15_2_14_3_1_1916 2 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 198 (accept_3_4 1 59 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 198 (allA_succ_of_accept 57 58 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 57 58 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 198 2 28 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 58 198 (Polychromatic418967fa.accept_15_10_13_3_1_4816 55 58 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 198 2 27 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 198 (accept_3_5 53 58 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 198 2 26 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 51 58 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 198 2 25 29 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 198
  (Polychromatic418967fa.accept_13_10_6_3_1_1515 49 58 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 198 2 24 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 58 198 (accept_3_5 47 58 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58
  198 2 23 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  58 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 58 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 58 198 2 22 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 58 198 (Polychromatic418967fa.accept_30_13_28_18_1_11516 43 58 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 198 2 21 29 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 198 (accept_3_5 41
  58 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 198 2 20 29 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 198
  (Polychromatic418967fa.accept_12_3_10_6_1_442 39 58 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 58 198 2 19 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 58 198 (Polychromatic418967fa.accept_19_18_1_8_1_7291 37 58 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 198 2 18 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 198 (accept_3_5 35 58 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 198 2 17 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 58 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 198 2 16 29 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 198
  (Polychromatic418967fa.accept_13_5_6_3_1_868 31 58 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 198 2 15 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 58 198 (accept_3_5 29 58 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58
  198 2 14 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  58 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 58 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 58 198 2 13 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 58 198 (Polychromatic418967fa.accept_15_10_13_3_1_4816 25 58 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 198 2 12 29 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 198 (accept_3_5 23 58 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 198 2 11 29 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 21 58 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 58 198 2 10 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 58 198 (Polychromatic418967fa.accept_27_19_4_9_1_9607 19 58 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 198 2 9 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 198 (accept_3_5 17 58 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 58 198 2 8 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 58 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 58 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 198 2 7 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 198 (Polychromatic418967fa.accept_17_13_7_11_1_3985
  13 58 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 198 2 6 29 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 198 (accept_3_5 11
  58 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 198 2 5 29 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 58 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 198 2 4 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 198 (Polychromatic418967fa.accept_19_7_1_8_1_7300 7 58 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 198 2 3 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 198 (accept_3_5 5 58 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 198 2 2 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 58 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 198 2 1 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 198 (Polychromatic418967fa.accept_13_1_6_3_1_1547 1
  58 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 198 (allA_succ_of_accept 56 57 198
  (Polychromatic418967fa.accept_12_8_9_6_1_127 56 57 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 57 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 198 3 18 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 198 (Polychromatic418967fa.accept_13_1_5_3_1_888 53
  57 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 52 57 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 198 3 17 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 50 57 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 49 57 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 198 3 16 19 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 57 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 57 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 198 3 15 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 44
  57 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 57 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 198 3 14 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 57 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 57 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 198 3 13 19 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 57 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 198 (Polychromatic418967fa.accept_13_11_5_3_1_889 37 57 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 198 3 12 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  57 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 34 57 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 198 3 11 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 57 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 198 3 10 19 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 198
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 57 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 57 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 198 3 9 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 57 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 198
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 25 57 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 198 3 8 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 57
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 198 3 7 19 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 57 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 198 3 6 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 57 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 57 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 198 3 5 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 57 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 57 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 198 3 4 19 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 57 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 198 3 3 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 57 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 198 3 2 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 198 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 57 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 57 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 198 3 1 19 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 198
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 57 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 198 (Polychromatic418967fa.accept_13_1_5_3_1_888 1 57 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 198))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  56 198 (allA_succ_of_accept 55 56 198 (accept_3_4 55 56 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  54 56 198 2 27 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 56 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 198 2 26 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 198 (Polychromatic418967fa.accept_12_3_8_6_1_895 51
  56 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 198 2 25 28 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 198 (accept_3_4 49
  56 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 198 2 24 28 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 198
  (Polychromatic418967fa.accept_19_9_18_8_1_8782 47 56 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 198 2 23 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 45 56 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 198 2 22 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 198 (accept_3_4 43 56 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 198 2 21 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 198 (Polychromatic418967fa.accept_17_7_5_11_1_2922 41 56 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 198 2 20 28 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 56 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 198 2 19 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 198 (accept_3_4 37 56 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56
  198 2 18 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  56 198 (Polychromatic418967fa.accept_19_16_18_8_1_8784 35 56 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 56 198 2 17 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 56 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 56 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 198 2 16 28 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 198 (accept_3_4 31 56 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 198 2 15 28 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 198
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 29 56 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 56 198 2 14 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 56 198 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 56 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 198 2 13 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 198 (accept_3_4 25 56 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 198 2 12 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 56 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 198 2 11 28 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 56 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 198 2 10 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 198 (accept_3_4 19 56 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  198 2 9 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 198 (Polychromatic418967fa.accept_21_17_14_9_1_8456 17 56 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 198 2 8 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 198 (Polychromatic418967fa.accept_12_3_8_6_1_895 15 56 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 198 2 7 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 198 (accept_3_4 13 56 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 198 2 6 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 56 198 (Polychromatic418967fa.accept_19_11_18_8_1_5911 11 56 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 198 2 5 28 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 56 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 198 2 4 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 56 198 (accept_3_4 7 56 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 198
  2 3 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56
  198 (Polychromatic418967fa.accept_20_5_16_18_1_10033 5 56 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 56 198 2 2 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 56 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 56 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 198 2 1 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 198 (accept_3_4 1 56 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 56 198)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 198
  (allA_succ_of_accept 54 55 198 (Polychromatic418967fa.accept_15_9_10_3_1_2845 54 55 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 198 (accept_3_5 53 55 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 55 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 198 (Polychromatic418967fa.accept_15_6_10_3_1_2844
  51 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 198 (accept_3_5 50
  55 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 198 (Polychromatic418967fa.accept_19_10_17_8_1_5917 48 55 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 198 (accept_3_5 47 55 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 55 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 55 198 11 4 5 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 55 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 55 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 55 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 198 (accept_3_5 41 55 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 55 198 (Polychromatic418967fa.accept_17_6_4_11_1_4072 40 55 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 198 (accept_3_5 38 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 55 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 198 (accept_3_5 35 55 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 198 (Polychromatic418967fa.accept_19_15_17_8_1_10101 34 55 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 55 198 11 3 5 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 55 198 (accept_3_5 32 55 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 31
  55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 198
  (Polychromatic418967fa.accept_19_11_17_8_1_7259 30 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 198 (accept_3_5 29 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 198 (Polychromatic418967fa.accept_15_13_10_3_1_1952 28 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 198 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 55 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 198 (accept_3_5 26 55 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 55 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 198 (accept_3_5 23 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 55
  198 11 2 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  55 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 55 198 (accept_3_5 20 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 55 198 (Polychromatic418967fa.accept_25_19_5_23_1_11515 19 55 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 55 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 198 (accept_3_5 17 55 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 198
  (Polychromatic418967fa.accept_19_16_17_8_1_8762 16 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 55 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 55 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 198 (accept_3_5 14 55 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 55 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 198 (Polychromatic418967fa.accept_10_2_5_8_1_139
  12 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 55 198 11 1 5 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 55 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 10 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 55 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 198 (accept_3_5 8 55 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 55 198 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 55 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 198 (Polychromatic418967fa.accept_15_6_10_3_1_2844
  6 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 198 (accept_3_5 5 55
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55 198 (Polychromatic418967fa.accept_7_4_6_2_1_451
  4 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 55 198 (accept_3_5 2 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55
  198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 55 198))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 198 (allA_succ_of_accept 53 54
  198 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 54 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 198 2 26 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 54 198 3 17 18 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 54 198 2 25 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 54 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 49 54 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 198 6 8 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 198 (Polychromatic418967fa.accept_19_9_16_8_1_2097 47 54 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 198 2 23 27 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 54 198 9 5 6 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 54 198 2 22 27 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 198
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 43 54 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 198 6 7 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 198 (Polychromatic418967fa.accept_21_20_12_9_1_11514 41 54 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 198 2 20 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 54 198 3 13 18 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 54 198 2 19 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 198 (Polychromatic418967fa.accept_13_11_2_3_1_883
  37 54 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 198 18 2 3 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 198
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 35 54 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 198 2 17 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 54 198 3 11 18 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 54 198 2 16 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 54 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 54 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 198 6 5 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 54 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 198 2 14 27 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 54 198 9 3 6 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 54 198 2 13 27 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 54 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 198 6 4 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 198 (Polychromatic418967fa.accept_13_10_2_3_1_3025 23 54 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 198 2 11 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 54 198 3 7 18 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 54 198 2 10 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 19
  54 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 198 18 1 3 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 54 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 54 198 2 8 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 54 198 3 5 18 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 54 198 2 7 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 198 (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 54 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 198 6 2 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 54 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 198 2 5 27 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 54 198 9 1 6 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 54 198 2 4 27 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 198
  (Polychromatic418967fa.accept_14_7_12_2_1_2502 7 54 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 198 6 1 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 198 (Polychromatic418967fa.accept_13_5_2_3_1_1526 5 54 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 198 2 2 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 54 198 3 1 18 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 54 198 2 1 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 198 (Polychromatic418967fa.accept_13_1_2_3_1_911 1 54 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 198 (allA_succ_of_accept 52 53 198 (accept_3_4
  52 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 198 (Polychromatic418967fa.accept_13_11_1_3_1_910 50 53 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 198 (accept_3_4 49 53 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 53 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  53 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 198 (accept_3_4 46 53
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 198
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 198 (Polychromatic418967fa.accept_13_5_1_3_1_878 44 53 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 198 (accept_3_4 43 53 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 198 (Polychromatic418967fa.accept_15_12_8_3_1_1995 42 53 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 198 (accept_3_4 40 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 198 (Polychromatic418967fa.accept_24_14_5_6_1_11512 38 53 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 198 (accept_3_4 37 53 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 53 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 198 (accept_3_4 34 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 198 (Polychromatic418967fa.accept_13_6_1_3_1_1522 32 53 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 198 (accept_3_4 31 53 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 198 (Polychromatic418967fa.accept_13_4_1_3_1_3058 30 53 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 198
  (Polychromatic418967fa.accept_27_2_26_9_1_11513 29 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 198 (accept_3_4 28 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 53 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 198 (accept_3_4 25 53 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 198 (Polychromatic418967fa.accept_13_11_1_3_1_910 24 53 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 198 (accept_3_4 22 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 198 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 53 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 198 (accept_3_4 19 53 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 198 (Polychromatic418967fa.accept_13_5_1_3_1_878 18 53 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 198
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 17 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 198 (accept_3_4 16 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 198 (Polychromatic418967fa.accept_24_14_5_6_1_11512 14 53 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 198 (accept_3_4 13 53 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 53 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 198 (accept_3_4 10 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 198 (Polychromatic418967fa.accept_14_9_11_2_1_2501 9 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 198 (Polychromatic418967fa.accept_17_8_2_11_1_4069 8 53 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 198 (accept_3_4 7 53 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 53 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 198 (accept_3_4 4 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 198 (Polychromatic418967fa.accept_13_2_1_3_1_419 2 53 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 198 (accept_3_4 1 53 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 198))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 198
  (allA_succ_of_accept 51 52 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 51 52 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 198 2 25 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 198 (Polychromatic418967fa.accept_15_4_7_3_1_119 49
  52 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 198 2 24 26 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 198 (accept_3_5 47
  52 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 198 2 23 26 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 52 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 52 198 2 22 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 52 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 52 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 52 198 2 21 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 52 198 (accept_3_5 41 52 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 198 2 20 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 52 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 52 198 2 19 26 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 52 198
  (Polychromatic418967fa.accept_16_5_4_6_1_3349 37 52 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 52 198 2 18 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 52 198 (accept_3_5 35 52 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52
  198 2 17 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  52 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 52 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 52 198 2 16 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 52 198 (Polychromatic418967fa.accept_23_8_6_14_1_11511 31 52 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 198 2 15 26 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 198 (accept_3_5 29 52 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 198 2 14 26 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 198
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 52 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 52 198 2 13 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 52 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 25 52 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 198 2 12 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 198 (accept_3_5 23 52 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 198 2 11 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 52 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 198 2 10 26 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 52 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 198 2 9 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 198 (accept_3_5 17 52 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52
  198 2 8 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  52 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 52 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 52 198 2 7 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 52 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 52 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 198 2 6 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 198 (accept_3_5 11 52 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 198 2 5 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 52 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 52 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 198 2 4 26 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 198
  (Polychromatic418967fa.accept_17_7_1_11_1_1894 7 52 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 52 198 2 3 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 52 198 (accept_3_5 5 52 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 198
  2 2 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52
  198 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 52 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 52 198 2 1 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 52 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 52 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 52 198)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 198
  (allA_succ_of_accept 50 51 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 50 51 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 51 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 198 3 16 17 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 198
  (Polychromatic418967fa.accept_20_7_11_18_1_7117 47 51 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 51 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 46 51 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 51 198 3 15 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 51 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 44
  51 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 198
  (Polychromatic418967fa.accept_10_3_1_8_1_132 43 51 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 51 198 3 14 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 51 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 51 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 40 51 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 198 3 13 17 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 51 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 51 198 3 12 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 51 198 (Polychromatic418967fa.accept_13_9_12_3_1_907
  35 51 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 198
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 51 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 51 198 3 11 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 51 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 51 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 198 (Polychromatic418967fa.accept_15_1_6_3_1_2827 31 51 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 198 3 10 17 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 51 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 51 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 198 3 9 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 51 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 51 198 3 8 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 51 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 51 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 51 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 198 3 7 17 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 198
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 51 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 198 (Polychromatic418967fa.accept_10_9_1_8_1_755 19 51 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 198 3 6 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 198
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 51 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 51 198 3 5 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 51 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 51 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 198 3 4 17 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 198
  (Polychromatic418967fa.accept_14_11_9_2_1_6382 11 51 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 51 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 198 3 3 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 51 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 198
  (Polychromatic418967fa.accept_14_7_9_2_1_2489 7 51 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 51 198 3 2 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 51 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 51 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 198 3 1 17 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 51 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 51 198))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 198
  (allA_succ_of_accept 49 50 198 (accept_3_4 49 50 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50
  198 2 24 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  50 198 (Polychromatic418967fa.accept_13_8_11_3_1_3053 47 50 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 50 198 2 23 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 50 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 50 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 198 2 22 25 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 198 (accept_3_4 43 50 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 198 2 21 25 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 50 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 198 2 20 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 39 50 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 198 2 19 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 198 (accept_3_4 37 50 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 198 2 18 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 50 198 (Polychromatic418967fa.accept_16_3_2_6_1_4461 35 50 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 198 2 17 25 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 50 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 198 2 16 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 50 198 (accept_3_4 31 50 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50
  198 2 15 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  50 198 (Polychromatic418967fa.accept_14_1_8_2_1_1675 29 50 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 50 198 2 14 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 50 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 50 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 198 2 13 25 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 198 (accept_3_4 25 50 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 198 2 12 25 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 198
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 23 50 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 198 2 11 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 50 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 50 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 198 2 10 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 198 (accept_3_4 19 50 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 198 2 9 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 50 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 50 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 198 2 8 25 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 50 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 50 198 2 7 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 50 198 (accept_3_4 13 50 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50
  198 2 6 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  50 198 (Polychromatic418967fa.accept_16_11_2_6_1_1435 11 50 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 50 198 2 5 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 50 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 50 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 198 2 4 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 198 (accept_3_4 7 50 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 198 2 3 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 50 198 (Polychromatic418967fa.accept_13_5_11_3_1_902 5 50 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 198 2 2 25 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 50 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 50 198 2 1 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 50 198 (accept_3_4 1 50 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  198)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 198 (allA_succ_of_accept 48 49 198
  (Polychromatic418967fa.accept_19_10_11_8_1_10121 48 49 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 49 198 (accept_3_5 47 49 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 49 198 (Polychromatic418967fa.accept_13_7_10_3_1_1505 46 49 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 198 (Polychromatic418967fa.accept_13_6_10_3_1_897 45 49 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 198 (accept_3_5 44 49 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  49 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 198
  (Polychromatic418967fa.accept_24_18_1_6_1_11510 42 49 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 198 (accept_3_5 41 49 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 198 (Polychromatic418967fa.accept_14_12_7_2_1_1663 40 49 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 198 (accept_3_5 38 49 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 198 (Polychromatic418967fa.accept_10_7_9_8_1_1135 37 49 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 198
  (Polychromatic418967fa.accept_19_17_11_8_1_11490 36 49 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 49 198 (accept_3_5 35 49 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 49 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 49 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 198 (Polychromatic418967fa.accept_13_7_10_3_1_1505 33 49
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 198 (accept_3_5 32 49 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  49 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 198
  (Polychromatic418967fa.accept_17_13_15_11_1_2936 30 49 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 49 198 (accept_3_5 29 49 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 49 198 (Polychromatic418967fa.accept_13_2_10_3_1_1538 28 49 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 198 (accept_3_5 26 49 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 198
  (Polychromatic418967fa.accept_23_2_3_14_1_11509 25 49 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 49 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 49 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 198 (accept_3_5 23 49 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 49 198 (Polychromatic418967fa.accept_15_7_4_3_1_1930 22 49 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 198 (Polychromatic418967fa.accept_10_1_9_8_1_123
  21 49 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 198 (accept_3_5 20
  49 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 49 198 (Polychromatic418967fa.accept_16_2_1_6_1_2342 18 49 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 198 (accept_3_5 17 49 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 49 198 (Polychromatic418967fa.accept_15_1_4_3_1_1928 16 49 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  49 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 198 (accept_3_5 14 49
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 198
  (Polychromatic418967fa.accept_17_13_15_11_1_2936 13 49 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 198 (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 49 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 198 (accept_3_5 11 49 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 198 (Polychromatic418967fa.accept_19_10_11_8_1_10121 10 49
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 198
  (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 49 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 198 (accept_3_5 8 49 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 198 (Polychromatic418967fa.accept_13_6_10_3_1_897 6 49 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 198 (accept_3_5 5 49 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 49 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 198 (accept_3_5 2 49 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 198 (Polychromatic418967fa.accept_10_1_9_8_1_123 1
  49 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  198))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 198 (allA_succ_of_accept 47 48 198
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 47 48 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 198 2 23 24 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 48 198 3 15 16 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 48 198 2 22 24 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 48 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 198 6 7 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 198 (Polychromatic418967fa.accept_13_2_9_3_1_2212 41 48 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 198 2 20 24 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 48 198 3 13 16 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 48 198 2 19 24 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 198
  (Polychromatic418967fa.accept_17_3_14_11_1_5243 37 48 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 198 6 6 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 198 (Polychromatic418967fa.accept_19_16_10_8_1_10067 35 48 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 198 2 17 24 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 48 198 3 11 16 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 48 198 2 16 24 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 31
  48 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 198 6 5 8 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 48 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 48 198 2 14 24 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 48 198 3 9 16 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 48 198 2 13 24 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 48 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 48 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 198 6 4 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 198 (Polychromatic418967fa.accept_19_4_10_8_1_11508 23 48
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 198 2 11 24 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 48 198 3 7 16 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 48 198 2 10 24 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 198
  (Polychromatic418967fa.accept_13_6_9_3_1_915 19 48 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 198 6 3 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 48 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 198 2 8 24 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 48 198 3 5 16 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 48 198 2 7 24 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 198 (Polychromatic418967fa.accept_20_13_8_18_1_8672 13 48
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 198 6 2 8 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 48 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 48 198 2 5 24 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 48 198 3 3 16 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 48 198 2 4 24 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 198 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 48 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 198 6 1 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 198 (Polychromatic418967fa.accept_13_5_9_3_1_870 5 48 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 198 2 2 24 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 48 198 3 1 16 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 48 198 2 1 24 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 48 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 198)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 198 (allA_succ_of_accept 46 47 198
  (accept_3_4 46 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 198 (Polychromatic418967fa.accept_13_5_8_3_1_1535 44 47 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 198 (accept_3_4 43 47 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 198 (Polychromatic418967fa.accept_15_12_2_3_1_1146 42 47 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 198 (accept_3_4 40 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 47 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 198 (accept_3_4 37 47 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 198 (Polychromatic418967fa.accept_19_17_9_8_1_3269 36 47 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 198
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 198 (accept_3_4 34 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 47 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 198 (accept_3_4 31 47 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 198 (Polychromatic418967fa.accept_19_11_9_8_1_11507 30 47 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 198 (accept_3_4 28 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 198 (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 198 (Polychromatic418967fa.accept_19_7_9_8_1_7297 26 47 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 198 (accept_3_4 25 47 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 47 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 198
  (Polychromatic418967fa.accept_16_7_15_6_1_1428 23 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 198 (accept_3_4 22 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 198 (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 47 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 198 (accept_3_4 19 47 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 47 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 198 (accept_3_4 16 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 198 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 198 (Polychromatic418967fa.accept_15_14_2_3_1_1980 14 47 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 198 (accept_3_4 13 47 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 198 (Polychromatic418967fa.accept_15_12_2_3_1_1146 12 47
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 198 (accept_3_4 10 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 47 198 (Polychromatic418967fa.accept_25_8_22_23_1_11506 8 47 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 198 (accept_3_4 7 47 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 47 198 (Polychromatic418967fa.accept_17_6_13_11_1_995 6 47 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 198 (accept_3_4 4 47 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 47
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 198
  (Polychromatic418967fa.accept_20_2_7_18_1_4145 2 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 198 (accept_3_4 1 47 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  198))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 198 (allA_succ_of_accept 45 46 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 45 46 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 46 198 2 22 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 46 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 46 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 198 2 21 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 198 (accept_3_5 41 46 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 198 2 20 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 46 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 198 2 19 23 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 198
  (Polychromatic418967fa.accept_13_11_7_3_1_894 37 46 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 198 2 18 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 46 198 (accept_3_5 35 46 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46
  198 2 17 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  46 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 46 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 46 198 2 16 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 46 198 (Polychromatic418967fa.accept_17_14_12_11_1_4063 31 46 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 198 2 15 23 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 198 (accept_3_5 29 46 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 198 2 14 23 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 46 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 46 198 2 13 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 46 198 (Polychromatic418967fa.accept_24_1_22_6_1_11505 25 46 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 198 2 12 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 198 (accept_3_5 23 46 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 198 2 11 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 46 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 198 2 10 23 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 46 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 198 2 9 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 198 (accept_3_5 17 46 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  198 2 8 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 46 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 198 2 7 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 46 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 46 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 198 2 6 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 198 (accept_3_5 11 46 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 198 2 5 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 46 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 46 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 46 198 2 4 23 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 46 198
  (Polychromatic418967fa.accept_25_7_21_23_1_11504 7 46 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 46 198 2 3 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 46 198 (accept_3_5 5 46 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 198
  2 2 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 46
  198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 46 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 46 198 2 1 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 46 198 (Polychromatic418967fa.accept_13_1_7_3_1_1503 1 46 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46 198)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45
  198 (allA_succ_of_accept 44 45 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 45 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 45 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 198 3 14 15 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 198
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 45 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 45 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 45 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 45 198 3 13 15 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 45 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 38
  45 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 198
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 37 45 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 45 198 9 4 5 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 45 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 45 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 45 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 198 3 11 15 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 45 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 198 3 10 15 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 29
  45 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 45 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 45 198 9 3 5 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 45 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 45 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 198 (Polychromatic418967fa.accept_16_9_13_6_1_2334 25 45
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 198 3 8 15 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 45 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 45 198 3 7 15 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 45 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 45 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 45 198 9 2 5 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 45 198 (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 45 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 45 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 198 3 5 15 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 198
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 45 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 45 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 198 3 4 15 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 198
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 45 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 45 198 9 1 5 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 45 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 45 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 198 3 2 15 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 45 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 45 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 45 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 45 198 3 1 15 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 45 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 45 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 45 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 198))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 198 (allA_succ_of_accept 43 44 198
  (accept_3_4 43 44 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 198 2 21 22 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 198
  (Polychromatic418967fa.accept_13_2_5_3_1_406 41 44 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 44 198 2 20 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 44 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 44 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 198 2 19 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 198 (accept_3_4 37 44 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 198 2 18 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 198 (Polychromatic418967fa.accept_13_9_5_3_1_428 35 44 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 198 2 17 22 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 44 198 11 3 4 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 44 198 2 16 22 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 198 (accept_3_4 31
  44 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 198 2 15 22 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 44 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 29 44 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 44 198 2 14 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 44 198 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 44 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 198 2 13 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 198 (accept_3_4 25 44 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 198 2 12 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 198 (Polychromatic418967fa.accept_27_23_17_9_1_11503 23 44
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 198 22 1 2 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 44 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 44 198 2 10 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 44 198 (accept_3_4 19 44 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44
  198 2 9 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  44 198 (Polychromatic418967fa.accept_15_2_14_3_1_1916 17 44 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 44 198 2 8 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 44 198 (Polychromatic418967fa.accept_12_3_8_6_1_895 15 44 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 198 2 7 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 198 (accept_3_4 13 44 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 198 2 6 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 11 44 198 11 1 4 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 44 198 2 5 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 44 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 44 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 198 2 4 22 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 198 (accept_3_4 7 44 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 198 2 3 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44 198 (Polychromatic418967fa.accept_25_5_19_23_1_11502 5 44 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 198 2 2 22 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 44 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 44 198 2 1 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 44 198 (accept_3_4 1 44 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  198)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 198 (allA_succ_of_accept 42 43 198
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 42 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 198 (accept_3_5 41 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 198 (Polychromatic418967fa.accept_13_1_4_3_1_1545 40 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 198 (Polychromatic418967fa.accept_15_9_13_3_1_535 39 43 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 198 (accept_3_5 38 43 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 198
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 198 (accept_3_5 35 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 198 (accept_3_5 32 43 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 43 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 198
  (Polychromatic418967fa.accept_23_7_20_14_1_11501 30 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 43 198 (accept_3_5 29 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 43 198 (Polychromatic418967fa.accept_20_8_3_18_1_11485 28 43 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 43 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 198 (accept_3_5 26 43 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  43 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 198 (accept_3_5 23 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 198 (Polychromatic418967fa.accept_14_8_1_2_1_965 22 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 198 (accept_3_5 20 43 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 198 (Polychromatic418967fa.accept_16_3_11_6_1_4467 19 43 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 198
  (Polychromatic418967fa.accept_16_2_11_6_1_737 18 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 198 (accept_3_5 17 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 43 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 198 (accept_3_5 14 43 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 198
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 198 (accept_3_5 11 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 198 (accept_3_5 8 43 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 198 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 43 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 198 (accept_3_5 5 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  198 (Polychromatic418967fa.accept_16_4_11_6_1_5591 4 43 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 43 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 43 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 198 (accept_3_5 2 43 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 198)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 42 198 (allA_succ_of_accept 41 42 198 (Polychromatic418967fa.accept_19_3_4_8_1_8808 41 42 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 198 2 20 21 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 42 198 3 13 14 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 42 198 2 19 21 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 198
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 37 42 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 198 6 6 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 42 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 42 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 198 2 17 21 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 42 198 3 11 14 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 42 198 2 16 21 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 198 (Polychromatic418967fa.accept_17_14_8_11_1_4052
  31 42 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 198 6 5 7 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 198
  (Polychromatic418967fa.accept_19_10_4_8_1_11500 29 42 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 198 2 14 21 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 42 198 3 9 14 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 42 198 2 13 21 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 42 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 25 42 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 198 6 4 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 198 (Polychromatic418967fa.accept_15_8_12_3_1_1912 23 42 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 198 2 11 21 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 198 3 7 14 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 198 2 10 21 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 198
  (Polychromatic418967fa.accept_17_2_8_11_1_1041 19 42 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 198 6 3 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 198 (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 42 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 198 2 8 21 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 42 198 3 5 14 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 42 198 2 7 21 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 198 (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 42
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 198 6 2 7 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 198
  (Polychromatic418967fa.accept_24_11_18_6_1_11499 11 42 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 42 198 2 5 21 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 42 198 3 3 14 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 42 198 2 4 21 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 42 198 (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 42 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 198 6 1 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 5
  42 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 198 2 2 21 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 42 198 3 1 14 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 42 198 2 1 21 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 198
  (Polychromatic418967fa.accept_17_1_8_11_1_6471 1 42 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 198)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 198 (allA_succ_of_accept 40 41 198
  (accept_3_4 40 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 41 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 198 (accept_3_4 37 41 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 41 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  41 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 198 (accept_3_4 34 41
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 198
  (Polychromatic418967fa.accept_10_3_1_8_1_132 33 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 41 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 198 (accept_3_4 31 41 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 198 (Polychromatic418967fa.accept_17_13_7_11_1_3985 30 41 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 198 (accept_3_4 28 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 198 (Polychromatic418967fa.accept_25_1_16_23_1_11498 26 41 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 198 (accept_3_4 25 41 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 41 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 198 (accept_3_4 22 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 198 (Polychromatic418967fa.accept_15_6_11_3_1_1172 21 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 198 (Polychromatic418967fa.accept_25_20_16_23_1_11497 20 41 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 198 (accept_3_4 19 41 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 41 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 198 (accept_3_4 16 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 198 (Polychromatic418967fa.accept_13_1_2_3_1_911 14 41 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 198 (accept_3_4 13 41 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 198 (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 41 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 198 (accept_3_4 10 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 198 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 41 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 198 (accept_3_4 7 41 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 198 (Polychromatic418967fa.accept_15_6_11_3_1_1172 6 41 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 198
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 5 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 198 (accept_3_4 4 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 198 (Polychromatic418967fa.accept_16_2_9_6_1_4441 2 41 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 198 (accept_3_4 1 41 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 198))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 198 (allA_succ_of_accept 39 40 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 40 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 198 2 19 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 198 (Polychromatic418967fa.accept_13_11_1_3_1_910 37 40 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 198 2 18 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 198 (accept_3_5 35 40 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 198 2 17 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 40 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 198 2 16 20 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 40 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 198 2 15 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 198 (accept_3_5 29 40 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  198 2 14 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  40 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 40 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 198 2 13 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 40 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 40 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 198 2 12 20 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 198 (accept_3_5 23 40 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 198 2 11 20 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 198
  (Polychromatic418967fa.accept_12_9_4_6_1_460 21 40 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 198 2 10 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 198 (Polychromatic418967fa.accept_13_6_1_3_1_1522 19 40 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 198 2 9 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 198 (accept_3_5 17 40 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 40 198 2 8 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 40 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 40 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 198 2 7 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 198 (Polychromatic418967fa.accept_15_13_10_3_1_1952
  13 40 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 198 2 6 20 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 198 (accept_3_5 11
  40 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 198 2 5 20 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 198
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 40 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 198 2 4 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 198 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 40 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 198 2 3 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 198 (accept_3_5 5 40 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 40 198 2 2 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 40 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 40 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 198 2 1 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 198 (Polychromatic418967fa.accept_19_1_2_8_1_10129 1
  40 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  198)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 198 (allA_succ_of_accept 38 39 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 39 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 39 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 198 3 12 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 198 (Polychromatic418967fa.accept_15_5_9_3_1_528 35
  39 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 34 39 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 198 3 11 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 39 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 198 (Polychromatic418967fa.accept_10_1_9_8_1_123 31 39 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 198 3 10 13 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 39 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 198 3 9 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 39 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 198 3 8 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 198 (Polychromatic418967fa.accept_14_9_11_2_1_2501 23 39 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 39 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 198 3 7 13 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 39 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 39 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 198 3 6 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 198
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 39 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 198 3 5 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 39 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 198 3 4 13 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 198
  (Polychromatic418967fa.accept_10_1_9_8_1_123 11 39 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 39 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 198 3 3 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 39 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 198
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 39 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 198 3 2 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 39 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 198 3 1 13 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 39 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 198))))))))))))))))))))))))))))))))))))))) (allB_succ 38 198
  (allA_succ_of_accept 37 38 198 (accept_3_4 37 38 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  198 2 18 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 198 (Polychromatic418967fa.accept_13_9_12_3_1_907 35 38 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 198 2 17 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 38 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 198 2 16 19 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 198 (accept_3_4 31 38 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 198 2 15 19 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 38 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 198 2 14 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 38 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 198 2 13 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 198 (accept_3_4 25 38 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 198 2 12 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 198 (Polychromatic418967fa.accept_17_6_4_11_1_4072 23 38 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 198 2 11 19 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 38 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 198 2 10 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 198 (accept_3_4 19 38 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  198 2 9 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 198 (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 38 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 198 2 8 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 38 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 198 2 7 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 198 (accept_3_4 13 38 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 198 2 6 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 198 (Polychromatic418967fa.accept_15_11_8_3_1_1943 11 38 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 198 2 5 19 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 38 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 198 2 4 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 198 (accept_3_4 7 38 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 198
  2 3 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  198 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 38 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 198 2 2 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 38 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 198 2 1 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 198 (accept_3_4 1 38 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 198)))))))))))))))))))))))))))))))))))))) (allB_succ 37 198 (allA_succ_of_accept 36 37 198
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 198 (accept_3_5 35 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 198 (Polychromatic418967fa.accept_13_8_11_3_1_3053 34 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 198 (Polychromatic418967fa.accept_13_7_11_3_1_1540 33 37 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 198 (accept_3_5 32 37 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 37 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 198
  (Polychromatic418967fa.accept_19_11_18_8_1_5911 30 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 198 (accept_3_5 29 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 198 (Polychromatic418967fa.accept_13_2_11_3_1_873 28 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 198 (accept_3_5 26 37 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 198 (Polychromatic418967fa.accept_10_5_7_8_1_1176 25 37 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 198
  (Polychromatic418967fa.accept_21_3_16_9_1_8528 24 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 198 (accept_3_5 23 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 198 (Polychromatic418967fa.accept_20_2_17_18_1_11496 22 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 198 (Polychromatic418967fa.accept_13_8_11_3_1_3053 21 37 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 198 (accept_3_5 20 37 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 198
  (Polychromatic418967fa.accept_13_5_11_3_1_902 18 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 198 (accept_3_5 17 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 198 (Polychromatic418967fa.accept_19_16_18_8_1_8784 16 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 198 (accept_3_5 14 37 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 198 (Polychromatic418967fa.accept_19_13_18_8_1_4493 13 37 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 198
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 198 (accept_3_5 11 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 198 (Polychromatic418967fa.accept_13_10_11_3_1_1518 10 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 37 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 198 (accept_3_5 8 37 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 198
  (Polychromatic418967fa.accept_21_6_16_9_1_5300 6 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 198 (accept_3_5 5 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  198 (Polychromatic418967fa.accept_14_4_9_2_1_95 4 37 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 198 (accept_3_5 2 37 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 198 (Polychromatic418967fa.accept_13_1_11_3_1_901 1 37 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 198))))))))))))))))))))))))))))))))))))) (allB_succ 36 198
  (allA_succ_of_accept 35 36 198 (Polychromatic418967fa.accept_15_5_6_3_1_525 35 36 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 198 2 17 18 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 36 198 3 11 12 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 36 198 2 16 18 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 31
  36 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 198 6 5 6 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 198
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 29 36 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 36 198 2 14 18 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 36 198 9 3 4 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 36 198 2 13 18 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 198 (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 36 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 198 6 4 6 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 36 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 198 2 11 18 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 36 198 3 7 12 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 36 198 2 10 18 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 198
  (Polychromatic418967fa.accept_13_6_10_3_1_897 19 36 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 198 18 1 2 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 36 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 198 2 8 18 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 36 198 3 5 12 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 36 198 2 7 18 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 36 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 198 6 2 6 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 198
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 36 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 36 198 2 5 18 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 36 198 9 1 4 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 36 198 2 4 18 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 198 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 36 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 198 6 1 6 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 198 (Polychromatic418967fa.accept_15_5_6_3_1_525 5 36 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 198 2 2 18 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 36 198 3 1 12 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 36 198 2 1 18 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 198
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 1 36 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 198)))))))))))))))))))))))))))))))))))) (allB_succ 35 198 (allA_succ_of_accept 34 35 198 (accept_3_4 34
  35 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 35 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 35 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 198 (accept_3_4 31 35 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 198 (Polychromatic418967fa.accept_19_11_16_8_1_2098 30 35 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 198 (accept_3_4 28 35 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  35 198 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 35 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 198 (Polychromatic418967fa.accept_14_12_7_2_1_1663 26 35 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 198 (accept_3_4 25 35 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 198 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 35 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 198
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 35 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 198 (accept_3_4 22 35 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 35 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 198 (Polychromatic418967fa.accept_13_7_9_3_1_1504 20 35 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 198 (accept_3_4 19 35 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 198 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 35 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 198 (accept_3_4 16 35 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 198 (Polychromatic418967fa.accept_13_2_9_3_1_2212 15 35 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 198 (Polychromatic418967fa.accept_25_14_10_23_1_11495 14 35 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 198 (accept_3_4 13 35 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 35 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 198
  (Polychromatic418967fa.accept_16_11_3_6_1_4462 11 35 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 198 (accept_3_4 10 35 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 198 (Polychromatic418967fa.accept_13_8_9_3_1_2213 8 35 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 198 (accept_3_4 7 35 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 198 (Polychromatic418967fa.accept_13_6_9_3_1_915 6 35 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 35
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 198 (accept_3_4 4 35 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 198 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3
  35 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 35 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 198 (accept_3_4 1 35 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  198))))))))))))))))))))))))))))))))))) (allB_succ 34 198 (allA_succ_of_accept 33 34 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 33 34 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 198 2 16 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 34 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 198 2 15 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 198 (accept_3_5 29 34 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 198 2 14 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 34 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 198 2 13 17 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 34 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 198 2 12 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 198 (accept_3_5 23 34 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34
  198 2 11 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  34 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 34 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 34 198 2 10 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 34 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 19 34 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 198 2 9 17 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 198 (accept_3_5 17 34 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34 198 2 8 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 34 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 198 2 7 17 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 198
  (Polychromatic418967fa.accept_25_13_9_23_1_11494 13 34 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 34 198 2 6 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 34 198 (accept_3_5 11 34 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 34 198 2 5 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 34 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 34 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 34 198 2 4 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 34 198 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 34 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 198 2 3 17 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 198 (accept_3_5 5 34 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 198 2 2 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 34 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 34
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 198 2 1 17 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 34 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 198)))))))))))))))))))))))))))))))))) (allB_succ 33 198 (allA_succ_of_accept 32 33 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 33 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 33 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 33 198 3 10 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 33 198
  (Polychromatic418967fa.accept_17_12_16_11_1_7885 29 33 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 33 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 33 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 198 3 9 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660
  26 33 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 33 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 33 198 3 8 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 33 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 33 198 11 2 3 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 33 198 3 7 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 33 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 33 198 3 6 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 33 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 33 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 33 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 198 3 5 11 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 198
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 33 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 198 (Polychromatic418967fa.accept_19_13_14_8_1_4490 13 33 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 198 3 4 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 33 198 11 1 3 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 33 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 33 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 198 3 3 11 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 198
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 33 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 198 3 2 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 33 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 33 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 198 3 1 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 33 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 198 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 33 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 198)))))))))))))))))))))))))))))))))
  (allB_succ 32 198 (allA_succ_of_accept 31 32 198 (accept_3_4 31 32 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 32 198 2 15 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 32 198 (Polychromatic418967fa.accept_15_14_2_3_1_1980 29 32 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 32 198 2 14 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 32 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 27
  32 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 198 2 13 16 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 198 (accept_3_4 25
  32 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 198 2 12 16 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 198
  (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 32 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 32 198 2 11 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 32 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 32 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 32 198 2 10 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 32 198 (accept_3_4 19 32 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 198 2 9 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 32 198 (Polychromatic418967fa.accept_23_17_9_14_1_8205 17 32 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 32 198 2 8 16 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 32 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 32 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 32 198 2 7 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 32 198 (accept_3_4 13 32 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32
  198 2 6 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  32 198 (Polychromatic418967fa.accept_27_11_5_9_1_11493 11 32 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 32 198 2 5 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 32 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 32 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 198 2 4 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 198 (accept_3_4 7 32 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 198 2 3 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 32 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 32 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 32 198 2 2 16 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 32 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 32 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 32 198 2 1 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 32 198 (accept_3_4 1 32 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32
  198)))))))))))))))))))))))))))))))) (allB_succ 31 198 (allA_succ_of_accept 30 31 198
  (Polychromatic418967fa.accept_19_11_12_8_1_11492 30 31 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 31 198 (accept_3_5 29 31 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 31 198 (Polychromatic418967fa.accept_13_2_5_3_1_406 28 31 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 31 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 198 (accept_3_5 26 31 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  31 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 198
  (Polychromatic418967fa.accept_13_11_5_3_1_889 24 31 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 198 (accept_3_5 23 31 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 31 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 198 (accept_3_5 20 31 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 31 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 198
  (Polychromatic418967fa.accept_21_18_10_9_1_5297 18 31 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 198 (accept_3_5 17 31 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 198 (Polychromatic418967fa.accept_17_16_14_11_1_7836 16 31 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 31 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 198 (accept_3_5 14 31 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 31 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 198 (accept_3_5 11 31 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 198 (Polychromatic418967fa.accept_19_10_12_8_1_10124 10 31 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 198 (accept_3_5 8 31 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 198 (Polychromatic418967fa.accept_16_7_15_6_1_1428 7 31 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 198
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 31 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 198 (accept_3_5 5 31 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  198 (Polychromatic418967fa.accept_15_4_1_3_1_1922 4 31 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 31 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 198 (accept_3_5 2 31 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 198))))))))))))))))))))))))))))))) (allB_succ 30 198
  (allA_succ_of_accept 29 30 198 (Polychromatic418967fa.accept_17_12_13_11_1_2910 29 30 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 198 2 14 15 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 30 198 3 9 10 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 30 198 2 13 15 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 198 (Polychromatic418967fa.accept_13_12_4_3_1_1528
  25 30 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 198 6 4 5 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 198
  (Polychromatic418967fa.accept_17_6_13_11_1_995 23 30 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 30 198 2 11 15 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 30 198 3 7 10 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 30 198 2 10 15 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 198 (Polychromatic418967fa.accept_23_19_7_14_1_11491 19 30 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 198 6 3 5 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 198 (Polychromatic418967fa.accept_19_17_11_8_1_11490 17 30
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 198 2 8 15 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 198 3 5 10 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 198 2 7 15 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 198
  (Polychromatic418967fa.accept_26_13_4_16_1_11489 13 30 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 30 198 6 2 5 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 30 198 (Polychromatic418967fa.accept_23_11_7_14_1_11488 11 30 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 198 2 5 15 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 30 198 3 3 10 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 30 198 2 4 15 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 198
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 30 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 30 198 6 1 5 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 30 198 (Polychromatic418967fa.accept_20_5_10_18_1_5622 5 30 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 198 2 2 15 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 30 198 3 1 10 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 30 198 2 1 15 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 198 (Polychromatic418967fa.accept_13_1_4_3_1_1545 1 30 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 198)))))))))))))))))))))))))))))) (allB_succ
  29 198 (allA_succ_of_accept 28 29 198 (accept_3_4 28 29 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 29 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 198 (Polychromatic418967fa.accept_15_11_14_3_1_1965 26 29
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 198 (accept_3_4 25 29 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 24
  29 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 29 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 198 (accept_3_4 22 29 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 198 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 29 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 29 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 198 (accept_3_4 19 29 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 198 (Polychromatic418967fa.accept_19_18_10_8_1_2088 18 29 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 29 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 198 (accept_3_4 16 29 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 29 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 198 (accept_3_4 13 29 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 198 (Polychromatic418967fa.accept_19_12_10_8_1_3270 12 29 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 198 (accept_3_4 10 29 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 198 (Polychromatic418967fa.accept_16_9_13_6_1_2334 9 29 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 198 (Polychromatic418967fa.accept_14_8_1_2_1_965 8 29 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 198 (accept_3_4 7 29 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 29 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 198
  (Polychromatic418967fa.accept_19_5_10_8_1_8775 5 29 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 198 (accept_3_4 4 29 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 198 (Polychromatic418967fa.accept_15_2_14_3_1_1916 2 29 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 198 (accept_3_4 1 29 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 198))))))))))))))))))))))))))))) (allB_succ 28 198 (allA_succ_of_accept 27 28 198
  (Polychromatic418967fa.accept_12_3_4_6_1_434 27 28 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 198 2 13 14 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 28 198 (Polychromatic418967fa.accept_13_12_2_3_1_1527 25 28 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 198 2 12 14 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 198 (accept_3_5 23 28 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 198 2 11 14 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 28 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 198 2 10 14 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 198
  (Polychromatic418967fa.accept_21_19_7_9_1_11487 19 28 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 198 2 9 14 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 198 (accept_3_5 17 28 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28
  198 2 8 14 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  28 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 28 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 28 198 2 7 14 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 28 198 (Polychromatic418967fa.accept_20_13_8_18_1_8672 13 28 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 198 2 6 14 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 198 (accept_3_5 11 28 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 198 2 5 14 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 28 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 198 2 4 14 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 198
  (Polychromatic418967fa.accept_19_7_9_8_1_7297 7 28 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 28 198 2 3 14 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 28 198 (accept_3_5 5 28 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 198
  2 2 14 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28
  198 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 28 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 198 2 1 14 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 198 (Polychromatic418967fa.accept_13_1_2_3_1_911 1 28 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 198)))))))))))))))))))))))))))) (allB_succ 27 198 (allA_succ_of_accept 26
  27 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 27 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 27 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 198 3 8 9 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 198 (Polychromatic418967fa.accept_15_8_12_3_1_1912
  23 27 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 22 27 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 198 3 7 9 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 27 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 19 27 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 198 9 2 3 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 27 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 198 3 5 9 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 27 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 198 3 4 9 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 27 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 27 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 198 9 1 3 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 27 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 198 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 27 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 198 3 2 9 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 4 27 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 198 3 1 9 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 27 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 198))))))))))))))))))))))))))) (allB_succ 26
  198 (allA_succ_of_accept 25 26 198 (accept_3_4 25 26 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24
  26 198 2 12 13 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  23 26 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 26 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 198 2 11 13 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 26 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 198 2 10 13 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 198 (accept_3_4 19 26 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 198 2 9 13 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 17
  26 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 198 2 8 13 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 26 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 198 2 7 13 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 198 (accept_3_4 13 26 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  198 2 6 13 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 26 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 198 2 5 13 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 26 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 198 2 4 13 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 198 (accept_3_4 7 26 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 198 2 3 13 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 198 (Polychromatic418967fa.accept_27_5_26_9_1_11486 5 26 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 198 2 2 13 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 26 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 198 2 1 13 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 198 (accept_3_4 1 26 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  198)))))))))))))))))))))))))) (allB_succ 25 198 (allA_succ_of_accept 24 25 198
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 24 25 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 198 (accept_3_5 23 25 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 25 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 198 (Polychromatic418967fa.accept_15_6_10_3_1_2844 21 25 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 198 (accept_3_5 20 25 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 25 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 198
  (Polychromatic418967fa.accept_16_2_9_6_1_4441 18 25 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 198 (accept_3_5 17 25 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 198 (Polychromatic418967fa.accept_19_16_6_8_1_8772 16 25 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 25 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 198 (accept_3_5 14 25 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 25 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 25 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 198 (accept_3_5 11 25 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 198 (Polychromatic418967fa.accept_20_10_5_18_1_5627 10 25 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 198 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 25 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 198 (accept_3_5 8 25 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 25 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 198 (accept_3_5 5 25 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  198 (Polychromatic418967fa.accept_13_4_12_3_1_2999 4 25 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 25 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 198 (accept_3_5 2 25 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 198 (Polychromatic418967fa.accept_17_1_8_11_1_6471 1 25 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 198))))))))))))))))))))))))) (allB_succ 24 198
  (allA_succ_of_accept 23 24 198 (Polychromatic418967fa.accept_13_10_11_3_1_1518 23 24 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 198 2 11 12 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 24 198 3 7 8 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 24 198 2 10 12 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 19
  24 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 198 6 3 4 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 198
  (Polychromatic418967fa.accept_21_17_3_9_1_8524 17 24 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 24 198 2 8 12 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 24 198 3 5 8 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 24 198 2 7 12 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 24 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 198 6 2 4 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 198 (Polychromatic418967fa.accept_23_11_1_14_1_6454 11 24
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 198 2 5 12 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 24 198 3 3 8 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 24 198 2 4 12 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 198
  (Polychromatic418967fa.accept_13_7_11_3_1_1540 7 24 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 198 6 1 4 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 24 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 198 2 2 12 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 24 198 3 1 8 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 24 198 2 1 12 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 24 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 198)))))))))))))))))))))))) (allB_succ 23
  198 (allA_succ_of_accept 22 23 198 (accept_3_4 22 23 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 23 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 23 198 (Polychromatic418967fa.accept_13_7_10_3_1_1505 20 23 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 198 (accept_3_4 19 23 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 23 198 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 23 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 23 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 198 (accept_3_4 16 23 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 23 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 198 (Polychromatic418967fa.accept_19_14_4_8_1_8807 14 23 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 198 (accept_3_4 13 23 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 198 (Polychromatic418967fa.accept_15_12_8_3_1_1995 12 23
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 198
  (Polychromatic418967fa.accept_10_1_3_8_1_136 11 23 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 198 (accept_3_4 10 23 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 198 (Polychromatic418967fa.accept_20_8_3_18_1_11485 8 23 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 198 (accept_3_4 7 23 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 23 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 198 (accept_3_4 4 23 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 198 (Polychromatic418967fa.accept_19_3_4_8_1_8808 3
  23 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 198
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 2 23 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 198 (accept_3_4 1 23 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  198))))))))))))))))))))))) (allB_succ 22 198 (allA_succ_of_accept 21 22 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 21 22 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 198 2 10 11 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 198 (Polychromatic418967fa.accept_13_6_9_3_1_915 19 22 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 198 2 9 11 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 198 (accept_3_5 17 22 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 198 2 8 11 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 22 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 198 2 7 11 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 13
  22 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 198 2 6 11 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 22 198 11 1 2 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 22 198 2 5 11 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 22 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 198 2 4 11 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 198 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 22 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 198 2 3 11 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 198 (accept_3_5 5 22 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 198 2 2 11 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 22 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 198 2 1 11 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 198 (Polychromatic418967fa.accept_14_1_8_2_1_1675 1
  22 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 198)))))))))))))))))))))) (allB_succ
  21 198 (allA_succ_of_accept 20 21 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 21 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  21 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 198 3 6 7 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 198
  (Polychromatic418967fa.accept_16_1_5_6_1_4435 17 21 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 21 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 198 3 5 7 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 21 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 198
  (Polychromatic418967fa.accept_10_3_1_8_1_132 13 21 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 198 3 4 7 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 21
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 198 3 3 7 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 198
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 21 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 198 3 2 7 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 198 (Polychromatic418967fa.accept_13_5_8_3_1_1535 5 21 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 21 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 198 3 1 7 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 21 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 198 (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 21 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 198))))))))))))))))))))) (allB_succ 20 198
  (allA_succ_of_accept 19 20 198 (accept_3_4 19 20 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20
  198 2 9 10 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  20 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 20 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 20 198 2 8 10 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 20 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 20 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 198 2 7 10 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 198 (accept_3_4 13 20 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 198 2 6 10 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 20 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 20 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 198 2 5 10 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 20 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 198 2 4 10 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 198 (accept_3_4 7 20 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 198
  2 3 10 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  198 (Polychromatic418967fa.accept_16_5_4_6_1_3349 5 20 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 20 198 2 2 10 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 20 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 20 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 198 2 1 10 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 198 (accept_3_4 1 20 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 20 198)))))))))))))))))))) (allB_succ 19 198 (allA_succ_of_accept 18 19 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 19 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 198 (accept_3_5 17 19 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 198 (Polychromatic418967fa.accept_15_1_4_3_1_1928 16 19 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 198 (Polychromatic418967fa.accept_21_15_19_9_1_2504 15 19 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 198 (accept_3_5 14 19 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 198
  (Polychromatic418967fa.accept_21_12_19_9_1_8442 12 19 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 198 (accept_3_5 11 19 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 19 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 198 (accept_3_5 8 19 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 198 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 19 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 198
  (Polychromatic418967fa.accept_25_6_19_23_1_11484 6 19 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 198 (accept_3_5 5 19 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  198 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 19 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 19 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 198 (accept_3_5 2 19 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 198))))))))))))))))))) (allB_succ 18 198 (allA_succ_of_accept 17
  18 198 (Polychromatic418967fa.accept_16_1_2_6_1_2295 17 18 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 18 198 2 8 9 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 18 198 3 5 6 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 18 198 2 7 9 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 18 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 18 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 198 6 2 3 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 198 (Polychromatic418967fa.accept_13_11_5_3_1_889
  11 18 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 198 2 5 9 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 18 198 9 1 2 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 18 198 2 4 9 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 198
  (Polychromatic418967fa.accept_17_7_1_11_1_1894 7 18 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 18 198 6 1 3 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 18 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 18 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 198 2 2 9 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 198 3 1 6 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 198 2 1 9 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 198 (Polychromatic418967fa.accept_13_1_5_3_1_888 1 18 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 198)))))))))))))))))) (allB_succ 17 198
  (allA_succ_of_accept 16 17 198 (accept_3_4 16 17 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 198 (Polychromatic418967fa.accept_13_1_4_3_1_1545 14 17 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 198 (accept_3_4 13 17 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 17 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 198 (accept_3_4 10 17 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 17 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 17 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 198 (accept_3_4 7 17 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 17 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 17 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 198 (accept_3_4 4 17 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 198 (Polychromatic418967fa.accept_16_2_1_6_1_2342 2 17 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 198 (accept_3_4 1 17 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 198))))))))))))))))) (allB_succ 16 198 (allA_succ_of_accept 15 16 198
  (Polychromatic418967fa.accept_12_3_4_6_1_434 15 16 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 198 2 7 8 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 16 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 198 2 6 8 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 198 (accept_3_5 11 16 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 198 2 5 8 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 16 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 198 2 4 8 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 198 (Polychromatic418967fa.accept_19_7_16_8_1_8761 7
  16 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 198 2 3 8 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 198 (accept_3_5 5 16
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 198 2 2 8 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 198
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 16 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 198 2 1 8 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 198 (Polychromatic418967fa.accept_19_1_16_8_1_10075 1 16 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 198)))))))))))))))) (allB_succ 15 198 (allA_succ_of_accept 14 15 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 15 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 198 3 4 5 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 198 (Polychromatic418967fa.accept_13_11_2_3_1_883 11 15 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 10 15 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 198 3 3 5 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 15 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 198 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 15 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 198 3 2 5 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 15 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 15 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 198 3 1 5 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 15 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 198))))))))))))))) (allB_succ 14 198 (allA_succ_of_accept 13 14 198 (accept_3_4 13 14 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 198 2 6 7 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 198 (Polychromatic418967fa.accept_13_11_1_3_1_910 11 14 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 198 2 5 7 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 14 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 14 198 2 4 7 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 14 198 (accept_3_4 7 14 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 14 198
  2 3 7 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14 198
  (Polychromatic418967fa.accept_13_5_1_3_1_878 5 14 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 14 198 2 2 7 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 14 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 14 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 198 2 1 7 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 198 (accept_3_4 1 14 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 198)))))))))))))) (allB_succ 13 198 (allA_succ_of_accept 12 13 198
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 13 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 198 (accept_3_5 11 13 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 13 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 198 (Polychromatic418967fa.accept_15_9_13_3_1_535 9 13 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 198 (accept_3_5 8 13 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 198
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 13 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 198 (accept_3_5 5 13 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  198 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 13 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 198 (accept_3_5 2 13 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 13 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 198))))))))))))) (allB_succ 12 198 (allA_succ_of_accept 11 12
  198 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 12 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 198 2 5 6 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 12 198 3 3 4 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 12 198 2 4 6 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 198 (Polychromatic418967fa.accept_14_7_12_2_1_2502 7 12 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 198 6 1 2 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 12 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 198 2 2 6 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 12 198 3 1 4 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 12 198 2 1 6 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 198
  (Polychromatic418967fa.accept_19_1_12_8_1_8799 1 12 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 198)))))))))))) (allB_succ 11 198 (allA_succ_of_accept 10 11 198 (accept_3_4 10 11 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 198
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 8 11 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 198 (accept_3_4 7 11 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  198 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 11 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 198 (accept_3_4 4 11 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 11 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 198 (Polychromatic418967fa.accept_13_2_11_3_1_873 2
  11 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 198 (accept_3_4 1 11 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 198))))))))))) (allB_succ 10 198 (allA_succ_of_accept 9 10 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 10 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 198 2 4 5 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 198 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 10 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 198 2 3 5 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 198 (accept_3_5 5 10 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 10 198 2 2 5 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 10 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 10 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 198 2 1 5 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 10
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 198)))))))))) (allB_succ 9 198
  (allA_succ_of_accept 8 9 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 9 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 9 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 198 3 2 3 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 198
  (Polychromatic418967fa.accept_13_5_9_3_1_870 5 9 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 9 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 198 3 1 3 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 9 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 198
  (Polychromatic418967fa.accept_10_1_9_8_1_123 1 9 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 198))))))))) (allB_succ 8 198 (allA_succ_of_accept 7 8 198 (accept_3_4 7 8 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 198 2 3 4 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 8 198 (Polychromatic418967fa.accept_13_5_8_3_1_1535 5 8 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 198 2 2 4 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 8 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 8 198 2 1 4 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 8 198 (accept_3_4 1 8 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 198))))))))
  (allB_succ 7 198 (allA_succ_of_accept 6 7 198 (Polychromatic418967fa.accept_19_6_7_8_1_10108 6 7 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 7 198 (accept_3_5 5 7 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 198 (Polychromatic418967fa.accept_13_4_7_3_1_92 4 7 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 7 198
  (Polychromatic418967fa.accept_21_3_7_9_1_8519 3 7 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 7 198 (accept_3_5 2 7 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 7 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 7 198))))))) (allB_succ 6 198 (allA_succ_of_accept 5 6 198 (Polychromatic418967fa.accept_13_5_6_3_1_868 5 6
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 198 2 2 3 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 6 198 3 1 2 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 6 198 2 1 3 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 6 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 198)))))) (allB_succ 5 198 (allA_succ_of_accept 4 5 198 (accept_3_4 4 5 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 5 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 5
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 198 (accept_3_4 1 5 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 198))))) (allB_succ 4 198 (allA_succ_of_accept 3 4 198
  (Polychromatic418967fa.accept_12_3_4_6_1_434 3 4 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 4 198 2 1 2 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 4 198 (Polychromatic418967fa.accept_13_1_4_3_1_1545 1 4 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 4 198)))) (allB_succ 3 198 (allA_succ_of_accept 2 3 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 3 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 198 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 3 198))) (allB_succ 2 198 (allA_succ_of_accept 1 2 198 (accept_3_4 1 2 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 2 198)) (allB_two
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


