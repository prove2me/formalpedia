-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch212_Segment000
-- name    : Polychromatic418967fa_Branch212_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:32:48.838391+00:00
-- url     : https://prove2.me/theorems/5a5da3e2-f4e6-4597-9f16-6abb9ae489be
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

def Polychromatic418967fa.branch_212_segment_000 : allB 128 212 :=
  allB_succ' 86 127 212 (Eq.refl Bool.true) (allA_of_3_0 86 127 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  87 126 212 (Eq.refl Bool.true) (allA_succ_of_gcd 86 126 212 2 43 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 126 212 (accept_3_2 85 126 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 84 126 212 2 42 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 126 212 (Polychromatic418967fa.accept_13_5_9_4_1_441 83 126 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 126 212 2 41 63 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 126 212
  (Polychromatic418967fa.accept_10_1_6_2_1_867 81 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 126 212 2 40 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 126 212 (accept_3_2 79 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 212 2 39 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 212 (Polychromatic418967fa.accept_20_17_6_12_1_8185 77 126 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 126 212 2 38 63 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 126 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 75 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 126 212 2 37 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 126 212 (accept_3_2 73 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 212 2 36 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 126 212 (Polychromatic418967fa.accept_10_1_6_2_1_867 71 126 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 126 212 2 35 63 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 126 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 126 212 2 34 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 126 212 (accept_3_2 67 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 212 2 33 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 212 (Polychromatic418967fa.accept_16_1_14_4_1_3220 65 126 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 126 212 2 32 63 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 126 212
  (Polychromatic418967fa.accept_11_8_5_3_1_694 63 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 126 212 2 31 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 126 212 (accept_3_2 61 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 212 2 30 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 212 (Polychromatic418967fa.accept_13_7_9_4_1_918 59 126 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 212 2 29 63 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 126 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 126 212 2 28 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 126 212 (accept_3_2 55 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 212 2 27 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 212 (Polychromatic418967fa.accept_15_8_6_2_1_1128 53 126 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 212 2 26 63 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 126 212
  (Polychromatic418967fa.accept_10_1_6_2_1_867 51 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 126 212 2 25 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 126 212 (accept_3_2 49 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 212 2 24 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 126 212 (Polychromatic418967fa.accept_13_8_9_4_1_1552 47 126 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 212 2 23 63 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 126 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 126 212 2 22 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 126 212 (accept_3_2 43 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 212 2 21 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 212 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 126 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 212 2 20 63 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 126 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 126 212 2 19 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 126 212 (accept_3_2 37 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 212 2 18 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 212 (Polychromatic418967fa.accept_17_1_7_8_1_6347 35 126 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 212 2 17 63 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 126 212 2 16 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 126 212 (accept_3_2 31 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 212 2 15 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 212 (Polychromatic418967fa.accept_19_10_12_3_1_12558 29 126 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 212 2 14 63 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 212 2 13 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 212 (accept_3_2 25 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 212 2 12 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 212 (Polychromatic418967fa.accept_15_8_6_2_1_1128 23 126 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 212 2 11 63 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 126 212
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 126 212 2 10 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 126 212 (accept_3_2 19 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 212 2 9 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 126 212 (Polychromatic418967fa.accept_16_1_14_4_1_3220 17 126 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 212 2 8 63 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 126 212 2 7 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 126 212 (accept_3_2 13 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 126 212 2 6 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 126 212 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 126 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 212 2 5 63 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 126 212 2 4 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 126 212 (accept_3_2 7 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126
  212 2 3 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  126 212 (Polychromatic418967fa.accept_13_5_9_4_1_441 5 126 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 126 212 2 2 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 126 212 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 126 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 212 2 1 63 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 212 (accept_3_2 1 126 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 125 212
  (Eq.refl Bool.true) (allA_succ_of_accept 87 125 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 125 212
  (Polychromatic418967fa.accept_12_2_5_8_1_159 86 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 125 212 (accept_3_2 85 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 125 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 125 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 83 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 125 212 (accept_3_2 82 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 125 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 125 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 80 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 125 212 (accept_3_2 79 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 125 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 125 212 (Polychromatic418967fa.accept_10_7_5_2_1_880 77 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 125 212 (accept_3_2 76 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 125 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 125 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 125 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 74 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 125 212 (accept_3_2 73 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 125 212 (Polychromatic418967fa.accept_15_12_5_2_1_2786 72 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 125 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 125 212 (accept_3_2 70 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 125 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 125 212
  (Polychromatic418967fa.accept_10_8_5_2_1_881 68 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 125 212 (accept_3_2 67 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 125 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 125 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 65 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 125 212 (accept_3_2 64 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 125 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 125 212
  (Polychromatic418967fa.accept_11_7_4_3_1_302 62 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 125 212 (accept_3_2 61 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 125 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 125 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 125 212 (accept_3_2 58 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 125 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 125 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 125 212 (accept_3_2 55 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 125 212 (Polychromatic418967fa.accept_16_6_13_4_1_643 54 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 125 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 212 (accept_3_2 52 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 125 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 125 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 125 212 (accept_3_2 49 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 125 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 125 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 212 (accept_3_2 46 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 125 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 125 212
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 44 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 125 212 (accept_3_2 43 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 125 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 212 (accept_3_2 40 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 125 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 125 212 (accept_3_2 37 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 125 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 212 (Polychromatic418967fa.accept_13_9_8_4_1_937 35 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 212 (accept_3_2 34 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 125 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 212 (accept_3_2 31 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 212 (accept_3_2 28 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 212
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 212 (accept_3_2 25 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 212 (Polychromatic418967fa.accept_10_3_5_2_1_38 23 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 212 (accept_3_2 22 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 212 (accept_3_2 19 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 212 (accept_3_2 16 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 212
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 212 (accept_3_2 13 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 212 (accept_3_2 10 125 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 212 (accept_3_2 7 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 212 (Polychromatic418967fa.accept_21_5_20_2_1_7948 5 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 212 (accept_3_2 4 125 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 125 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 212 (accept_3_2 1 125 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 124 212
  (Eq.refl Bool.true) (allA_of_3_0 89 124 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 123 212 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 123 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 123 212 (accept_3_2 88 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 123 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 123 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 123 212
  (Polychromatic418967fa.accept_16_6_11_4_1_635 86 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 123 212 (accept_3_2 85 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 123 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 123 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 123 212 (accept_3_2 82 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 123 212 (Polychromatic418967fa.accept_10_1_3_2_1_220 81 123 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 123 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 80 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 123 212 (accept_3_2 79 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 123 212 (Polychromatic418967fa.accept_11_1_2_3_1_688 78 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 123 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 123 212 (accept_3_2 76 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 123 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 123 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 123 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 74 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 123 212 (accept_3_2 73 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 123 212 (Polychromatic418967fa.accept_13_7_6_4_1_933 72 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 123 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 123 212 (accept_3_2 70 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 123 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 123 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 123 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 68 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 123 212 (accept_3_2 67 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 123 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 123 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 212 (accept_3_2 64 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 123 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 123 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 123 212
  (Polychromatic418967fa.accept_7_6_4_2_1_236 62 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 123 212 (accept_3_2 61 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 123 212 (Polychromatic418967fa.accept_16_12_11_4_1_1359 60 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 123 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 212 (accept_3_2 58 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 123 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 123 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 123 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 123 212 (accept_3_2 55 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 123 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 123 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 212 (accept_3_2 52 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 123 212 (Polychromatic418967fa.accept_10_1_3_2_1_220 51 123 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 212
  (Polychromatic418967fa.accept_13_11_6_4_1_3121 50 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 123 212 (accept_3_2 49 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 123 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 123 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 212 (accept_3_2 46 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 123 212 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 123 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 123 212 (accept_3_2 43 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 123 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 123 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 212 (accept_3_2 40 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 123 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 123 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 123 212 (accept_3_2 37 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 123 212 (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 123 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 212 (accept_3_2 34 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 123 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 123 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 123 212
  (Polychromatic418967fa.accept_19_13_9_3_1_9806 32 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 123 212 (accept_3_2 31 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 123 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 123 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 212 (accept_3_2 28 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 123 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 123 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 123 212 (accept_3_2 25 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 123 212 (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 123 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 212 (accept_3_2 22 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 123 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 212
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 123 212 (accept_3_2 19 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 123 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 123 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 212 (accept_3_2 16 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 123 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 212
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 123 212 (accept_3_2 13 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 123 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 123 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 212 (accept_3_2 10 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 212 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 123 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 212 (accept_3_2 7 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  123 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 123 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 212 (accept_3_2 4 123 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 123 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 212 (accept_3_2 1 123 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 122 212
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 122 212 2 45 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 122 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 122 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 122 212 2 44 61 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 122 212
  (Polychromatic418967fa.accept_13_9_5_4_1_1591 87 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 122 212 2 43 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 122 212 (accept_3_2 85 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 122 212 2 42 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 122 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 122 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 122 212 2 41 61 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 122 212
  (Polychromatic418967fa.accept_17_13_3_8_1_6310 81 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 122 212 2 40 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 122 212 (accept_3_2 79 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 122 212 2 39 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 122 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 122 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 122 212 2 38 61 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 122 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 75 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 122 212 2 37 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 122 212 (accept_3_2 73 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 122 212 2 36 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 122 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 122 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 122 212 2 35 61 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 122 212
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 122 212 2 34 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 122 212 (accept_3_2 67 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 122 212 2 33 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 122 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 122 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 122 212 2 32 61 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 212
  (Polychromatic418967fa.accept_17_12_3_8_1_7627 63 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 122 212 2 31 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 122 212 (accept_3_2 61 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 212 2 30 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 122 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 212 2 29 61 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 212 2 28 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 212 (accept_3_2 55 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 212 2 27 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 122 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 212 2 26 61 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 212
  (Polychromatic418967fa.accept_13_12_5_4_1_3133 51 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 212 2 25 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 212 (accept_3_2 49 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 212 2 24 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 122 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 212 2 23 61 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 212
  (Polychromatic418967fa.accept_13_6_5_4_1_3924 45 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 212 2 22 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 212 (accept_3_2 43 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 212 2 21 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 122 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 212 2 20 61 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 212
  (Polychromatic418967fa.accept_17_5_3_8_1_1697 39 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 212 2 19 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 212 (accept_3_2 37 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 212 2 18 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 212 (Polychromatic418967fa.accept_11_2_1_3_1_683 35 122 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 212 2 17 61 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 212 2 16 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 212 (accept_3_2 31 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 212 2 15 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 122 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 212 2 14 61 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 212
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 212 2 13 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 212 (accept_3_2 25 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 212 2 12 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 122 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 212 2 11 61 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 212
  (Polychromatic418967fa.accept_23_21_7_5_1_12557 21 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 122 212 2 10 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 122 212 (accept_3_2 19 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 212 2 9 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 122 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 122 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 212 2 8 61 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 122 212 2 7 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 122 212 (accept_3_2 13 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 122 212 2 6 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 122 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 122 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 122 212 2 5 61 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 122 212
  (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 122 212 2 4 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 122 212 (accept_3_2 7 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122
  212 2 3 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  122 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 122 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 122 212 2 2 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 122 212 (Polychromatic418967fa.accept_21_3_17_2_1_11043 3 122 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 212 2 1 61 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 212 (accept_3_2 1 122 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 121 212
  (Eq.refl Bool.true) (allA_of_3_0 92 121 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 120 212 (Eq.refl
  Bool.true) (allA_succ_of_gcd 92 120 212 4 23 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 120 212 (accept_3_2 91 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 120 212 2 45 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 120 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 89 120 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 120 212 4 22 30 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 120 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 87 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 120 212 2 43 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 120 212 (accept_3_2 85 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 120 212 4 21 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 120 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 120 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 120 212 2 41 60 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 120 212
  (Polychromatic418967fa.accept_16_1_8_4_1_4334 81 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 120 212 4 20 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 120 212 (accept_3_2 79 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 120 212 2 39 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 120 212 (Polychromatic418967fa.accept_13_12_3_4_1_928 77 120 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 120 212 4 19 30 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 120 212
  (Polychromatic418967fa.accept_16_11_8_4_1_2234 75 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 120 212 2 37 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 120 212 (accept_3_2 73 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 212 4 18 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 120 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 120 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 120 212 2 35 60 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 120 212
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 120 212 4 17 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 120 212 (accept_3_2 67 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 212 2 33 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 120 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 120 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 120 212 4 16 30 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 120 212
  (Polychromatic418967fa.accept_16_15_8_4_1_1355 63 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 120 212 2 31 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 120 212 (accept_3_2 61 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 212 4 15 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 120 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 212 2 29 60 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 120 212
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 57 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 120 212 4 14 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 120 212 (accept_3_2 55 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 212 2 27 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 120 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 120 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 212 4 13 30 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 120 212
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 120 212 2 25 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 120 212 (accept_3_2 49 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 212 4 12 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 120 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 212 2 23 60 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 120 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 120 212 4 11 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 120 212 (accept_3_2 43 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 212 2 21 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 120 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 212 4 10 30 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 120 212
  (Polychromatic418967fa.accept_16_7_8_4_1_689 39 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 120 212 2 19 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 120 212 (accept_3_2 37 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 212 4 9 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 120 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 120 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 212 2 17 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 33
  120 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 120 212 4 8 30 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 212 (accept_3_2 31
  120 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 212 2 15 60 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 120 212 4 7 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 120 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 120 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 212 2 13 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 212 (accept_3_2 25 120 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 212 4 6 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 212 (Polychromatic418967fa.accept_16_7_8_4_1_689 23 120 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 212 2 11 60 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 212
  (Polychromatic418967fa.accept_16_5_8_4_1_5418 21 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 212 4 5 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 120 212 (accept_3_2 19 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  120 212 2 9 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 120 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 212 4 4 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 120 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  120 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 212 2 7 60 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 212 (accept_3_2 13
  120 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 212 4 3 30 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 212 2 5 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 120 212 (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 120 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 120 212 4 2 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 212 (accept_3_2 7 120 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 212 2 3 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 212 (Polychromatic418967fa.accept_16_5_8_4_1_5418 5 120 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 212 4 1 30 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 120 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 120 212 2 1 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 120 212 (accept_3_2 1 120 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 119
  212 (Eq.refl Bool.true) (allA_succ_of_accept 93 119 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 119 212
  (Polychromatic418967fa.accept_16_12_7_4_1_687 92 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 119 212 (accept_3_2 91 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 119 212 (Polychromatic418967fa.accept_13_12_2_4_1_3131 90 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 119 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 89 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 212 (accept_3_2 88 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 119 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 212
  (Polychromatic418967fa.accept_12_2_11_8_1_504 86 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 119 212 (accept_3_2 85 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 119 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 119 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 83 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 212 (accept_3_2 82 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 119 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 119 212
  (Polychromatic418967fa.accept_9_8_2_5_1_237 80 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 119 212 (accept_3_2 79 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 119 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 119 212 (Polychromatic418967fa.accept_10_7_9_2_1_1887 77 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 119 212 (accept_3_2 76 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 119 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 119 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 212
  (Polychromatic418967fa.accept_12_2_11_8_1_504 74 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 119 212 (accept_3_2 73 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 119 212 (Polychromatic418967fa.accept_11_6_9_3_1_1103 72 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 119 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 119 212 (accept_3_2 70 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 119 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 212
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 68 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 119 212 (accept_3_2 67 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 119 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 119 212 (Polychromatic418967fa.accept_14_9_7_2_1_2483 65 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 212 (accept_3_2 64 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 119 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 212
  (Polychromatic418967fa.accept_9_8_2_5_1_237 62 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 119 212 (accept_3_2 61 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 119 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 119 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 59 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 212 (accept_3_2 58 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 212
  (Polychromatic418967fa.accept_16_8_7_4_1_2217 56 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 119 212 (accept_3_2 55 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 119 212 (Polychromatic418967fa.accept_14_12_7_2_1_1663 54 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 212 (accept_3_2 52 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 212
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 50 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 212 (accept_3_2 49 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 212 (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 212 (accept_3_2 46 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 119 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 212
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 212 (accept_3_2 43 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 212 (Polychromatic418967fa.accept_10_1_9_2_1_45 41 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 212 (accept_3_2 40 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 212
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 212 (accept_3_2 37 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 212 (Polychromatic418967fa.accept_19_17_5_3_1_5455 36 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 212 (accept_3_2 34 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 212
  (Polychromatic418967fa.accept_13_6_2_4_1_923 32 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 212 (accept_3_2 31 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 212 (Polychromatic418967fa.accept_16_13_7_4_1_3248 29 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 212 (accept_3_2 28 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 212
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 212 (accept_3_2 25 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 212 (Polychromatic418967fa.accept_14_9_7_2_1_2483 23 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 212 (accept_3_2 22 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 119 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 212
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 20 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 212 (accept_3_2 19 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 212 (Polychromatic418967fa.accept_13_5_2_4_1_3955 18 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 212 (accept_3_2 16 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 212
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 212 (accept_3_2 13 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 212 (accept_3_2 10 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 212
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 212 (accept_3_2 7 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 212 (Polychromatic418967fa.accept_13_5_2_4_1_3955 5 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 212 (accept_3_2 4 119 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 212
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 212 (accept_3_2 1 119 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 118
  212 (Eq.refl Bool.true) (allA_of_3_0 95 118 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 96 117 212
  (Eq.refl Bool.true) (allA_succ_of_accept 95 117 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 117 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 212 (accept_3_2 94 117 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 212 (Polychromatic418967fa.accept_15_3_12_2_1_507 93 117
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 117 212
  (Polychromatic418967fa.accept_11_4_7_3_1_289 92 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 117 212 (accept_3_2 91 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 117 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 117 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 212 (accept_3_2 88 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 117 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 212
  (Polychromatic418967fa.accept_16_6_5_4_1_4330 86 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 117 212 (accept_3_2 85 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 117 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 84 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 117 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 212 (accept_3_2 82 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 117 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 80 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 117 212 (accept_3_2 79 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 117 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 117 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 212 (accept_3_2 76 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 212 (Polychromatic418967fa.accept_10_5_7_2_1_516 75 117 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 74 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 117 212 (accept_3_2 73 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 117 212 (Polychromatic418967fa.accept_16_8_5_4_1_674 72 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 117 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 212 (accept_3_2 70 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 212 (Polychromatic418967fa.accept_10_9_7_2_1_887 69 117 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 212
  (Polychromatic418967fa.accept_23_22_2_5_1_10978 68 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 117 212 (accept_3_2 67 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 117 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 117 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 117 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 212 (accept_3_2 64 117 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 212 (Polychromatic418967fa.accept_14_7_5_2_1_2473
  63 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 212
  (Polychromatic418967fa.accept_20_2_17_12_1_5178 62 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 117 212 (accept_3_2 61 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 117 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 117 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 117 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 212 (accept_3_2 58 117 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 212 (Polychromatic418967fa.accept_8_1_5_4_1_388
  57 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 212
  (Polychromatic418967fa.accept_16_8_5_4_1_674 56 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 117 212 (accept_3_2 55 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 117 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 117 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 212 (accept_3_2 52 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 117 212 (Polychromatic418967fa.accept_15_6_12_2_1_2803 51 117 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 212
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 50 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 212 (accept_3_2 49 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 117 212 (Polychromatic418967fa.accept_11_4_7_3_1_289 48 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 117 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 212 (accept_3_2 46 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 117 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 212
  (Polychromatic418967fa.accept_10_4_7_2_1_211 44 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 117 212 (accept_3_2 43 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 117 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 117 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 212 (accept_3_2 40 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 117 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 212 (accept_3_2 37 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 117 212 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 117 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 212 (accept_3_2 34 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 117 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 212 (accept_3_2 31 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 117 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 117 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 212 (accept_3_2 28 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 212 (Polychromatic418967fa.accept_17_10_15_8_1_6324 27 117 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 212
  (Polychromatic418967fa.accept_11_4_7_3_1_289 26 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 212 (accept_3_2 25 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 117 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 117 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 212 (accept_3_2 22 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 212 (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 117 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 212
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 212 (accept_3_2 19 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 212 (accept_3_2 16 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 212 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 117 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 212
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 212 (accept_3_2 13 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 117 212 (Polychromatic418967fa.accept_16_12_5_4_1_3275 12 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 212 (accept_3_2 10 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 117 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 212
  (Polychromatic418967fa.accept_16_8_5_4_1_674 8 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 212 (accept_3_2 7 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 212 (accept_3_2 4 117 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 117 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 212
  (Polychromatic418967fa.accept_20_2_17_12_1_5178 2 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 212 (accept_3_2 1 117 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 116
  212 (Eq.refl Bool.true) (allA_succ_of_gcd 96 116 212 4 24 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 116 212 (Polychromatic418967fa.accept_15_5_11_2_1_1095 95 116
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 116 212 2 47 58 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 116 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 93 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 116 212 4 23 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 116 212 (accept_3_2 91 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 116 212 2 45 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 116 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 89 116 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 116 212 4 22 29 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 116 212
  (Polychromatic418967fa.accept_9_6_8_5_1_837 87 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 116 212 2 43 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 116 212 (accept_3_2 85 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 116 212 4 21 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 116 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 83 116 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 116 212 2 41 58 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 116 212
  (Polychromatic418967fa.accept_10_1_6_2_1_867 81 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 116 212 4 20 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 116 212 (accept_3_2 79 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 116 212 2 39 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 116 212 (Polychromatic418967fa.accept_18_5_8_14_1_1282 77 116 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 116 212 4 19 29 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 116 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 116 212 2 37 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 116 212 (accept_3_2 73 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 116 212 4 18 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 116 212 (Polychromatic418967fa.accept_10_1_6_2_1_867 71 116 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 116 212 2 35 58 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 116 212
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 116 212 4 17 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 116 212 (accept_3_2 67 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 116 212 2 33 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 116 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 116 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 116 212 4 16 29 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 116 212
  (Polychromatic418967fa.accept_11_8_6_3_1_661 63 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 116 212 2 31 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 116 212 (accept_3_2 61 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 116 212 4 15 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 212 (Polychromatic418967fa.accept_13_7_12_4_1_450 59 116 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 212 2 29 58 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 212 4 14 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 212 (accept_3_2 55 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 212 2 27 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 212 (Polychromatic418967fa.accept_11_9_6_3_1_1668 53 116 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 212 4 13 29 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 212
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 212 2 25 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 212 (accept_3_2 49 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 212 4 12 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 116 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 212 2 23 58 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 212
  (Polychromatic418967fa.accept_17_11_14_8_1_2729 45 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 116 212 4 11 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 116 212 (accept_3_2 43 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 212 2 21 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 116 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 212 4 10 29 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 212 2 19 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 212 (accept_3_2 37 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 212 4 9 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 116 212 (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 116 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 212 2 17 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 33
  116 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 116 212 4 8 29 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 116 212 (accept_3_2 31
  116 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 116 212 2 15 58 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 116 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 116 212 4 7 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 116 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 116 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 116 212 2 13 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 116 212 (accept_3_2 25 116 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 116 212 4 6 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 116 212 (Polychromatic418967fa.accept_14_9_4_2_1_983 23 116 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 212 2 11 58 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 212 4 5 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 116 212 (accept_3_2 19 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  116 212 2 9 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 116 212 (Polychromatic418967fa.accept_19_17_2_3_1_4190 17 116 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 212 4 4 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 15
  116 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 212 2 7 58 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 212 (accept_3_2 13
  116 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 212 4 3 29 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 116 212 2 5 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 116 212 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 116 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 212 4 2 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 212 (accept_3_2 7 116 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116 212 2 3 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 116 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 116 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 212 4 1 29 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 116 212 2 1 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 116 212 (accept_3_2 1 116 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  115 212 (Eq.refl Bool.true) (allA_of_3_0 98 115 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 99 114 212
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 114 212 2 49 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 114 212 (accept_3_2 97 114 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 114 212 2 48 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 114 212 (Polychromatic418967fa.accept_11_7_4_3_1_302 95 114 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 114 212 2 47 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 114 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 93 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 114 212 2 46 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 114 212 (accept_3_2 91 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 212 2 45 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 89 114 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 114 212 2 44 57 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 114 212
  (Polychromatic418967fa.accept_10_7_4_2_1_903 87 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 114 212 2 43 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 114 212 (accept_3_2 85 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 212 2 42 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 83 114 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 114 212 2 41 57 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 114 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 114 212 2 40 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 114 212 (accept_3_2 79 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 212 2 39 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 212 (Polychromatic418967fa.accept_10_7_4_2_1_903 77 114 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 114 212 2 38 57 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 114 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 75 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 114 212 2 37 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 114 212 (accept_3_2 73 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 212 2 36 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 71 114 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 114 212 2 35 57 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 114 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 114 212 2 34 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 114 212 (accept_3_2 67 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 212 2 33 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 114 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 212 2 32 57 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 114 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 114 212 2 31 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 114 212 (accept_3_2 61 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 212 2 30 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 212 (Polychromatic418967fa.accept_13_7_10_4_1_919 59 114 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 212 2 29 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 114 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 57 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 114 212 2 28 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 114 212 (accept_3_2 55 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 212 2 27 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 114 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 212 2 26 57 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 114 212
  (Polychromatic418967fa.accept_11_7_4_3_1_302 51 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 114 212 2 25 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 114 212 (accept_3_2 49 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 212 2 24 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 114 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 212 2 23 57 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 114 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 114 212 2 22 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 114 212 (accept_3_2 43 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 212 2 21 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 212 (Polychromatic418967fa.accept_15_11_9_2_1_4780 41 114 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 212 2 20 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 114 212 2 19 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 212 (accept_3_2 37 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 212 2 18 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 114 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 212 2 17 57 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 212 2 16 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 212 (accept_3_2 31 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 212 2 15 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 114 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 212 2 14 57 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 212
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 114 212 2 13 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 114 212 (accept_3_2 25 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 212 2 12 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 212 (Polychromatic418967fa.accept_15_8_9_2_1_1897 23 114 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 212 2 11 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 212 2 10 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 114 212 (accept_3_2 19 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 212 2 9 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 114 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 114 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 212 2 8 57 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 114 212 2 7 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 114 212 (accept_3_2 13 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 212 2 6 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 114 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 114 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 212 2 5 57 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 212 2 4 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 212 (accept_3_2 7 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114
  212 2 3 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  114 212 (Polychromatic418967fa.accept_13_5_10_4_1_1564 5 114 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 212 2 2 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 114 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 114 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 212 2 1 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 212 (accept_3_2 1 114 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  113 212 (Eq.refl Bool.true) (allA_succ_of_accept 99 113 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 113 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 212
  (Polychromatic418967fa.accept_12_2_5_8_1_159 98 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 212 (accept_3_2 97 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 212 (Polychromatic418967fa.accept_13_5_9_4_1_441 96 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 212 (Polychromatic418967fa.accept_10_5_3_2_1_899 95 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 212 (accept_3_2 94 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 113 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 212
  (Polychromatic418967fa.accept_14_8_1_2_1_965 92 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 113 212 (accept_3_2 91 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 113 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 113 212 (Polychromatic418967fa.accept_21_5_8_2_1_11063 89 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 212 (accept_3_2 88 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 113 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 212
  (Polychromatic418967fa.accept_12_2_5_8_1_159 86 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 212 (accept_3_2 85 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 212 (Polychromatic418967fa.accept_13_6_9_4_1_2288 84 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 113 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 113 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 212 (accept_3_2 82 113 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 80 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 212 (accept_3_2 79 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 212 (Polychromatic418967fa.accept_14_8_1_2_1_965 78 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 212 (Polychromatic418967fa.accept_8_5_1_4_1_628 77 113 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 212 (accept_3_2 76 113 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 212
  (Polychromatic418967fa.accept_12_2_5_8_1_159 74 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 212 (accept_3_2 73 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 212 (Polychromatic418967fa.accept_13_7_9_4_1_918 72 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 212 (Polychromatic418967fa.accept_10_1_3_2_1_220 71 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 212 (accept_3_2 70 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 113 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 212
  (Polychromatic418967fa.accept_19_11_18_3_1_1755 68 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 113 212 (accept_3_2 67 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 113 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 113 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 113 212 (Polychromatic418967fa.accept_10_5_3_2_1_899 65 113
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 212 (accept_3_2 64 113
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 212
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 113 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 113 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 212 (accept_3_2 61 113 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 113 212 (Polychromatic418967fa.accept_13_8_9_4_1_1552 60 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 113 212 (accept_3_2 58 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 113 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 113 212 (Polychromatic418967fa.accept_16_8_1_4_1_6622 56 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 212 (accept_3_2 55 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 212 (Polychromatic418967fa.accept_15_9_8_2_1_1109 54 113
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 212
  (Polychromatic418967fa.accept_8_5_1_4_1_628 53 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 113 212 (accept_3_2 52 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 113 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 212 (accept_3_2 49 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 113 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 212
  (Polychromatic418967fa.accept_13_8_9_4_1_1552 47 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 212 (accept_3_2 46 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 212 (Polychromatic418967fa.accept_13_5_9_4_1_441 44 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 212 (accept_3_2 43 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 212 (Polychromatic418967fa.accept_19_4_18_3_1_5553 42 113
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 212
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 212 (accept_3_2 40 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 113 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 212 (accept_3_2 37 113 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 212 (Polychromatic418967fa.accept_14_8_1_2_1_965 36 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 212
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 212 (accept_3_2 34 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 212 (Polychromatic418967fa.accept_13_6_9_4_1_2288 32 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 212 (accept_3_2 31 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 212 (Polychromatic418967fa.accept_16_14_1_4_1_5432 30 113
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 212
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 113 212 (accept_3_2 28 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 113 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 212 (accept_3_2 25 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 113 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 212
  (Polychromatic418967fa.accept_19_4_18_3_1_5553 23 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 212 (accept_3_2 22 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 113 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 212 (accept_3_2 19 113 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 212 (Polychromatic418967fa.accept_13_5_9_4_1_441 18 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 212 (accept_3_2 16 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 212 (accept_3_2 13 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 212 (Polychromatic418967fa.accept_16_12_1_4_1_5403 12 113
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 212
  (Polychromatic418967fa.accept_10_1_3_2_1_220 11 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 212 (accept_3_2 10 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 212 (Polychromatic418967fa.accept_13_8_9_4_1_1552 8 113 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 212 (accept_3_2 7 113 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 113 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 212
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 212 (accept_3_2 4 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 113 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 113 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 212 (accept_3_2 1 113 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 112 212 (Eq.refl Bool.true) (allA_of_3_0 101 112 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 102 111
  212 (Eq.refl Bool.true) (allA_succ_of_accept 101 111 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 101 111 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 111 212 (accept_3_2 100 111 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 111 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 99
  111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 111 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 98 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 111 212 (accept_3_2 97 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 111 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 96 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 111 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 111 212 (accept_3_2 94 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 111 212 (Polychromatic418967fa.accept_10_3_1_2_1_521 93 111 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 111 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 92 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 111 212 (accept_3_2 91 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 111 212 (Polychromatic418967fa.accept_11_2_1_3_1_683 90 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 111 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 111 212 (accept_3_2 88 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 111 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 111 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 111 212
  (Polychromatic418967fa.accept_10_6_1_2_1_874 86 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 111 212 (accept_3_2 85 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 111 212 (Polychromatic418967fa.accept_13_6_7_4_1_2264 84 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 111 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 111 212 (accept_3_2 82 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 111 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 111 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 111 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 80 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 111 212 (accept_3_2 79 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 111 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 111 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 111 212 (accept_3_2 76 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 111 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 111 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 74 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 111 212 (accept_3_2 73 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 111 212 (Polychromatic418967fa.accept_15_12_6_2_1_2760 72 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 111 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 212 (accept_3_2 70 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 111 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 111 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 212
  (Polychromatic418967fa.accept_11_2_1_3_1_683 68 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 111 212 (accept_3_2 67 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 111 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 111 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 212 (accept_3_2 64 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 111 212 (Polychromatic418967fa.accept_10_3_1_2_1_521 63 111 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 62 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 111 212 (accept_3_2 61 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 111 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 111 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 212 (accept_3_2 58 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 111 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 111 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 111 212 (accept_3_2 55 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 111 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 111 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 212 (accept_3_2 52 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 111 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 212 (accept_3_2 49 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 111 212 (Polychromatic418967fa.accept_13_9_7_4_1_953 48 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 111 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 212 (accept_3_2 46 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 111 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 111 212 (accept_3_2 43 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 111 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 111 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 212 (accept_3_2 40 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 111 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 111 212 (accept_3_2 37 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 111 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 111 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 212 (accept_3_2 34 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 111 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 111 212 (accept_3_2 31 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 111 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 111 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 212 (accept_3_2 28 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 111 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 212 (accept_3_2 25 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 111 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 111 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 212 (accept_3_2 22 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 212 (Polychromatic418967fa.accept_16_5_15_4_1_9099 21 111 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 212 (accept_3_2 19 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 111 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 111 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 212 (accept_3_2 16 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 111 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 212
  (Polychromatic418967fa.accept_16_14_15_4_1_3268 14 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 111 212 (accept_3_2 13 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 111 212 (Polychromatic418967fa.accept_13_12_7_4_1_3124 12 111 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 212 (accept_3_2 10 111 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 212 (Polychromatic418967fa.accept_10_9_1_2_1_522 9
  111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 212 (accept_3_2 7 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 212 (accept_3_2 4 111 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 111 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 212 (accept_3_2 1 111 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 110 212 (Eq.refl Bool.true) (allA_succ_of_gcd 102 110 212 2 51 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 110 212 (Polychromatic418967fa.accept_7_3_5_2_1_17
  101 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 110 212 2 50 55 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 110 212
  (Polychromatic418967fa.accept_23_7_18_5_1_12556 99 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 110 212 2 49 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 110 212 (accept_3_2 97 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 110 212 2 48 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 110 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 95 110 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 110 212 2 47 55 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 110 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 93 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 110 212 2 46 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 110 212 (accept_3_2 91 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 110 212 2 45 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 110 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 89 110 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 110 212 2 44 55 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 110 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 87 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 110 212 2 43 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 110 212 (accept_3_2 85 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 110 212 2 42 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 110 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 110 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 110 212 2 41 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 110 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 81 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 110 212 2 40 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 110 212 (accept_3_2 79 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 110 212 2 39 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 110 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 110 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 110 212 2 38 55 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 110 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 75 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 110 212 2 37 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 110 212 (accept_3_2 73 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 110 212 2 36 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 110 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 110 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 110 212 2 35 55 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 110 212
  (Polychromatic418967fa.accept_9_6_2_5_1_506 69 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 110 212 2 34 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 110 212 (accept_3_2 67 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 110 212 2 33 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 110 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 110 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 110 212 2 32 55 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 212
  (Polychromatic418967fa.accept_13_11_6_4_1_3121 63 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 110 212 2 31 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 110 212 (accept_3_2 61 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 212 2 30 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 110 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 212 2 29 55 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 57 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 212 2 28 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 110 212 (accept_3_2 55 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 110 212 2 27 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 110 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 110 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 212 2 26 55 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 212
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 212 2 25 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 212 (accept_3_2 49 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 212 2 24 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 110 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 212 2 23 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 110 212 2 22 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 110 212 (accept_3_2 43 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 212 2 21 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 110 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 212 2 20 55 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 212 2 19 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 212 (accept_3_2 37 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 212 2 18 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 110 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 212 2 17 55 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 212
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 212 2 16 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 212 (accept_3_2 31 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 212 2 15 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 110 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 212 2 14 55 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 212
  (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 212 2 13 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 212 (accept_3_2 25 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 212 2 12 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 110 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 212 2 11 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 212 2 10 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 212 (accept_3_2 19 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 212 2 9 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 110 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 110 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 212 2 8 55 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 212
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 110 212 2 7 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 110 212 (accept_3_2 13 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 110 212 2 6 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 110 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 110 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 212 2 5 55 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 212
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 212 2 4 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 212 (accept_3_2 7 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  212 2 3 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  110 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 110 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 110 212 2 2 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 110 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 110 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 212 2 1 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 212 (accept_3_2 1 110 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 109 212 (Eq.refl Bool.true) (allA_of_3_0 104 109 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 105 108
  212 (Eq.refl Bool.true) (allA_succ_of_gcd 104 108 212 4 26 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 108 212 (accept_3_2 103 108 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 108 212 2 51 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 108 212 (Polychromatic418967fa.accept_16_5_12_4_1_4325 101 108 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 108 212 4 25 27 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 108 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 99 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 108 212 2 49 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 108 212 (accept_3_2 97 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 212 4 24 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 108 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 95 108 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 108 212 2 47 54 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 108 212
  (Polychromatic418967fa.accept_16_13_12_4_1_4323 93 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 108 212 4 23 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 108 212 (accept_3_2 91 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 108 212 2 45 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 108 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 108 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 108 212 4 22 27 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 108 212
  (Polychromatic418967fa.accept_15_12_3_2_1_2756 87 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 108 212 2 43 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 108 212 (accept_3_2 85 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 212 4 21 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 108 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 108 212 2 41 54 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 108 212
  (Polychromatic418967fa.accept_16_1_12_4_1_695 81 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 108 212 4 20 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 108 212 (accept_3_2 79 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 212 2 39 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 212 (Polychromatic418967fa.accept_16_13_12_4_1_4323 77 108 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 108 212 4 19 27 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 108 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 75 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 108 212 2 37 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 108 212 (accept_3_2 73 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 212 4 18 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 108 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 212 2 35 54 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 108 212
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 108 212 4 17 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 108 212 (accept_3_2 67 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 212 2 33 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 65 108 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 212 4 16 27 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 108 212
  (Polychromatic418967fa.accept_16_15_12_4_1_4324 63 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 108 212 2 31 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 108 212 (accept_3_2 61 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 212 4 15 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 212 (Polychromatic418967fa.accept_15_14_3_2_1_2811 59 108 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 212 2 29 54 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 108 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 108 212 4 14 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 108 212 (accept_3_2 55 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 212 2 27 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 212 (Polychromatic418967fa.accept_16_5_12_4_1_4325 53 108 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 212 4 13 27 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 108 212
  (Polychromatic418967fa.accept_16_3_12_4_1_170 51 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 108 212 2 25 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 108 212 (accept_3_2 49 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 212 4 12 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 108 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 212 2 23 54 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 108 212
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 108 212 4 11 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 108 212 (accept_3_2 43 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 212 2 21 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 108 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 212 4 10 27 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 108 212
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 39 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 108 212 2 19 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 108 212 (accept_3_2 37 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 212 4 9 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 108 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 212 2 17 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 33
  108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 212 4 8 27 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 212 (accept_3_2 31
  108 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 108 212 2 15 54 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 108 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 212 4 7 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 108 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 108 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 212 2 13 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 212 (accept_3_2 25 108 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 212 4 6 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 212 (Polychromatic418967fa.accept_16_7_12_4_1_1347 23 108
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 212 2 11 54 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 212
  (Polychromatic418967fa.accept_16_5_12_4_1_4325 21 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 108 212 4 5 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 108 212 (accept_3_2 19 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  108 212 2 9 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 212 (Polychromatic418967fa.accept_11_6_9_3_1_1103 17 108 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 212 4 4 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 212 2 7 54 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 212 (accept_3_2 13
  108 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 212 4 3 27 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 212
  (Polychromatic418967fa.accept_16_11_12_4_1_3195 11 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 108 212 2 5 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 108 212 (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 108 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 212 4 2 27 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 212 (accept_3_2 7 108 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 212 2 3 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 5
  108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 212 4 1 27 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 108 212
  (Polychromatic418967fa.accept_16_3_12_4_1_170 3 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 108 212 2 1 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 212 (accept_3_2 1 108 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 107 212 (Eq.refl Bool.true) (allA_succ_of_accept 105 107 212
  (Polychromatic418967fa.accept_6_3_5_2_1_12 105 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 107 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 104 107 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 212 (accept_3_2 103 107 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 107 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 102 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 107 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 101 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 107 212 (accept_3_2 100 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 107 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 107 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 98 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 107 212 (accept_3_2 97 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 107 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 96 107 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 107 212
  (Polychromatic418967fa.accept_8_7_3_4_1_404 95 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 107 212 (accept_3_2 94 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 107 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 107 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 92 107 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 107 212 (accept_3_2 91 107 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 107 212 (Polychromatic418967fa.accept_13_12_3_4_1_928 90 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 107 212
  (Polychromatic418967fa.accept_10_9_7_2_1_887 89 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 107 212 (accept_3_2 88 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 107 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 107 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 86 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 107 212 (accept_3_2 85 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 107 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 107 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 107 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 83 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 107 212 (accept_3_2 82 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 107 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 107 212 (Polychromatic418967fa.accept_17_12_5_8_1_7680 80 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 107 212 (accept_3_2 79 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 107 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 107 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 107 212
  (Polychromatic418967fa.accept_13_12_3_4_1_928 77 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 107 212 (accept_3_2 76 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 107 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 107 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 74 107 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 107 212 (accept_3_2 73 107 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 107 212 (Polychromatic418967fa.accept_11_6_8_3_1_2236 72 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 107 212
  (Polychromatic418967fa.accept_8_7_3_4_1_404 71 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 107 212 (accept_3_2 70 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 107 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 107 212 (Polychromatic418967fa.accept_19_11_12_3_1_8407 68 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 107 212 (accept_3_2 67 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 107 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 107 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 107 212 (accept_3_2 64 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 107 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 107 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 212 (accept_3_2 61 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 107 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 107 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 212
  (Polychromatic418967fa.accept_10_9_7_2_1_887 59 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 107 212 (accept_3_2 58 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 107 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 107 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 107 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 212 (accept_3_2 55 107 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 107 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 212
  (Polychromatic418967fa.accept_13_1_3_4_1_925 53 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 107 212 (accept_3_2 52 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 107 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 107 212 (Polychromatic418967fa.accept_11_6_8_3_1_2236 50 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 212 (accept_3_2 49 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 107 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 212
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 212 (accept_3_2 46 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 212 (accept_3_2 43 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 107 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 212
  (Polychromatic418967fa.accept_16_9_11_4_1_3194 41 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 212 (accept_3_2 40 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 107 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 212 (accept_3_2 37 107 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 212 (Polychromatic418967fa.accept_19_17_12_3_1_12555 36 107 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 212
  (Polychromatic418967fa.accept_10_5_7_2_1_516 35 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 212 (accept_3_2 34 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 212 (Polychromatic418967fa.accept_14_4_9_2_1_95 32 107 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 212 (accept_3_2 31 107 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 212 (accept_3_2 28 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 212 (accept_3_2 25 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 107 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 212
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 212 (accept_3_2 22 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 107 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 212 (accept_3_2 19 107 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 212 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 212
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 212 (accept_3_2 16 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 212 (accept_3_2 13 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 107 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 212 (accept_3_2 10 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 212 (Polychromatic418967fa.accept_16_8_11_4_1_3290 8 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 212 (accept_3_2 7 107 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 107 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 212
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 212 (accept_3_2 4 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 107 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 212 (accept_3_2 1 107 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 212 (allA_of_3_0 106 106 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 212
  (allA_succ_of_accept 104 105 212 (Polychromatic418967fa.accept_16_8_9_4_1_630 104 105 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 212 (accept_3_2 103 105 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 105 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 102 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 105 212 (accept_3_2 100 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 105 212 (Polychromatic418967fa.accept_25_24_5_12_1_12554 99 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 98 105 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 98 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 212 (accept_3_2 97 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 212 (Polychromatic418967fa.accept_11_8_6_3_1_661 96 105
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 212 (accept_3_2 94 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 105 212 (Polychromatic418967fa.accept_8_5_1_4_1_628 93 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 105 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 92 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 212 (accept_3_2 91 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 212 (accept_3_2 88 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 212 (Polychromatic418967fa.accept_10_7_5_2_1_880 87 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 212 (Polychromatic418967fa.accept_11_9_6_3_1_1668 86 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 212 (accept_3_2 85 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 105 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 212 (accept_3_2 82 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 105 212 (Polychromatic418967fa.accept_13_3_1_4_1_945 81 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 105 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 80 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 212 (accept_3_2 79 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 212 (Polychromatic418967fa.accept_10_8_5_2_1_881 78 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 212 (accept_3_2 76 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 105 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 105 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 74 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 212 (accept_3_2 73 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 212 (Polychromatic418967fa.accept_16_8_9_4_1_630 72 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 212 (accept_3_2 70 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 105 212 (Polychromatic418967fa.accept_8_5_1_4_1_628 69 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 105 212 (Polychromatic418967fa.accept_10_8_5_2_1_881 68 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 212 (accept_3_2 67 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 105 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 105 212 (accept_3_2 64 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 105 212 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 105 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 62 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 212 (accept_3_2 61 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 212 (Polychromatic418967fa.accept_16_12_9_4_1_4345 60 105 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 212 (accept_3_2 58 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 105 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 105 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 212 (accept_3_2 55 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 212 (accept_3_2 52 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 105 212 (Polychromatic418967fa.accept_14_9_7_2_1_2483 51 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 105 212 (Polychromatic418967fa.accept_19_12_10_3_1_5503 50 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 212 (accept_3_2 49 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 105 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 212 (accept_3_2 46 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 105 212 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 105 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 212 (accept_3_2 43 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 212 (Polychromatic418967fa.accept_11_9_6_3_1_1668 42 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 212 (accept_3_2 40 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 105 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 105 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 212 (accept_3_2 37 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 212 (Polychromatic418967fa.accept_13_10_1_4_1_3103 36 105 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 212 (accept_3_2 34 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 105 212 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 105 212 (Polychromatic418967fa.accept_19_13_10_3_1_11235 32 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 212 (accept_3_2 31 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 105 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 212 (accept_3_2 28 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 105 212 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 105 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 212 (accept_3_2 25 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 212 (Polychromatic418967fa.accept_16_8_9_4_1_630 24 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 212 (accept_3_2 22 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 212 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 105 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 212 (accept_3_2 19 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 212 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 212 (accept_3_2 16 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 212 (Polychromatic418967fa.accept_19_15_10_3_1_12550 15 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 212 (Polychromatic418967fa.accept_16_14_9_4_1_6693 14 105 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 212 (accept_3_2 13 105 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 12
  105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 212 (accept_3_2 10 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 212 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 212 (accept_3_2 7 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 105 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 212 (accept_3_2 4 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 105 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 212 (accept_3_2 1 105 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 212 (allA_succ_of_accept 103 104 212 (accept_3_2 103 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 104 212 2 51 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 104 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 101 104 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 104 212 4 25 26 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 104 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 99 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 104 212 2 49 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 104 212 (accept_3_2 97 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 104 212 4 24 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 104 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 95 104 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 104 212 2 47 52 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 104 212
  (Polychromatic418967fa.accept_15_3_14_2_1_1888 93 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 104 212 4 23 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 104 212 (accept_3_2 91 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 104 212 2 45 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 104 212 (Polychromatic418967fa.accept_16_9_8_4_1_1354 89 104 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 104 212 4 22 26 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 104 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 87 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 104 212 2 43 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 104 212 (accept_3_2 85 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 104 212 4 21 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 104 212 (Polychromatic418967fa.accept_16_3_8_4_1_3279 83 104 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 104 212 2 41 52 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 104 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 81 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 104 212 4 20 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 104 212 (accept_3_2 79 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 104 212 2 39 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 104 212 (Polychromatic418967fa.accept_10_7_4_2_1_903 77 104 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 212 4 19 26 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 212
  (Polychromatic418967fa.accept_16_11_8_4_1_2234 75 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 104 212 2 37 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 104 212 (accept_3_2 73 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 104 212 4 18 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 104 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 104 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 212 2 35 52 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 212
  (Polychromatic418967fa.accept_16_5_8_4_1_5418 69 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 104 212 4 17 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 104 212 (accept_3_2 67 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 104 212 2 33 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 104 212 (Polychromatic418967fa.accept_15_5_14_2_1_1876 65 104 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 104 212 4 16 26 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 104 212
  (Polychromatic418967fa.accept_11_8_5_3_1_694 63 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 104 212 2 31 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 104 212 (accept_3_2 61 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 104 212 4 15 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 104 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 104 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 212 2 29 52 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 212 4 14 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 104 212 (accept_3_2 55 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 212 2 27 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 104 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 212 4 13 26 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 212
  (Polychromatic418967fa.accept_16_3_8_4_1_3279 51 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 212 2 25 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 212 (accept_3_2 49 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 212 4 12 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 104 212 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 104 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 212 2 23 52 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 104 212 4 11 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 104 212 (accept_3_2 43 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 212 2 21 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 212 (Polychromatic418967fa.accept_11_8_5_3_1_694 41 104 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 212 4 10 26 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 212 2 19 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 212 (accept_3_2 37 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 212 4 9 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 104 212 (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 104 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 212 2 17 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 212 (Polychromatic418967fa.accept_15_3_14_2_1_1888
  33 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 104 212 4 8 26 53
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 104 212
  (accept_3_2 31 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 104 212 2 15 52 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 104 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 104 212 4 7 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 104 212 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 104 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 104 212 2 13 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 104 212 (accept_3_2 25 104 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 104 212 4 6 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 104 212 (Polychromatic418967fa.accept_16_7_8_4_1_689 23 104 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 212 2 11 52 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 212
  (Polychromatic418967fa.accept_16_5_8_4_1_5418 21 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 212 4 5 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 104 212 (accept_3_2 19 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  104 212 2 9 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 104 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 212 4 4 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  104 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 212 2 7 52 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 212 (accept_3_2 13
  104 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 212 4 3 26 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 212 2 5 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 104 212 (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 104 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 212 4 2 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 212 (accept_3_2 7 104 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104 212 2 3 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 104 212 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 104 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 212 4 1 26 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 104 212 2 1 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 104 212 (accept_3_2 1 104 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 212 (allA_of_3_0 103 103 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 212 (allA_succ_of_accept 101
  102 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 101 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 102 212 2 50 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 102 212 (Polychromatic418967fa.accept_12_3_6_8_1_969 99 102 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 102 212 2 49 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 212 (accept_3_2 97 102 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 102 212 2 48 51 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 102 212
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 95 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 102 212 2 47 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 102 212 (Polychromatic418967fa.accept_12_9_6_8_1_518 93 102 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 102 212 2 46 51 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 212 (accept_3_2 91 102 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 102 212 2 45 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 102 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 89
  102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 102 212 2 44 51 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 102 212
  (Polychromatic418967fa.accept_9_6_3_5_1_240 87 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 102 212 2 43 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 102 212 (accept_3_2 85 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 212 2 42 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 83 102 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 102 212 2 41 51 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 102 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 102 212 2 40 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 102 212 (accept_3_2 79 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 212 2 39 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 212 (Polychromatic418967fa.accept_13_12_11_4_1_3111 77 102 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 212 2 38 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 102 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 102 212 2 37 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 102 212 (accept_3_2 73 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 212 2 36 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 102 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 212 2 35 51 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 102 212
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 102 212 2 34 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 102 212 (accept_3_2 67 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 212 2 33 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 102 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 212 2 32 51 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 102 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 102 212 2 31 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 102 212 (accept_3_2 61 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 212 2 30 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 212 (Polychromatic418967fa.accept_13_7_11_4_1_2247 59 102 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 212 2 29 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 102 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 102 212 2 28 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 102 212 (accept_3_2 55 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 212 2 27 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 102 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 212 2 26 51 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 102 212
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 102 212 2 25 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 102 212 (accept_3_2 49 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 212 2 24 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 102 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 212 2 23 51 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 102 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 102 212 2 22 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 102 212 (accept_3_2 43 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 212 2 21 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 102 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 212 2 20 51 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 212 2 19 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 212 (accept_3_2 37 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 212 2 18 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 102 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 212 2 17 51 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 102 212 2 16 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 102 212 (accept_3_2 31 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 212 2 15 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 102 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 212 2 14 51 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 212
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 212 2 13 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 212 (accept_3_2 25 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 212 2 12 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 212 (Polychromatic418967fa.accept_13_10_11_4_1_2248 23 102 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 212 2 11 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 212 2 10 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 212 (accept_3_2 19 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 212 2 9 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 102 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 102 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 212 2 8 51 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 212
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 102 212 2 7 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 102 212 (accept_3_2 13 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 212 2 6 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 102 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 102 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 212 2 5 51 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 212 2 4 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 212 (accept_3_2 7 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102
  212 2 3 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  102 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 102 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 212 2 2 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 102 212 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 102 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 212 2 1 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 212 (accept_3_2 1 102 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 212 (allA_succ_of_accept 100 101 212 (accept_3_2 100 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 101 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 98 101 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 212 (accept_3_2 97 101 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 212 (Polychromatic418967fa.accept_7_5_3_2_1_249
  96 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 101 212
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 95 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 101 212 (accept_3_2 94 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 101 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 101 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 92 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 212 (accept_3_2 91 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 90 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 89 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 101 212 (accept_3_2 88 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 101 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 101 212 (Polychromatic418967fa.accept_10_6_1_2_1_874 86 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 212 (accept_3_2 85 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 101 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 212
  (Polychromatic418967fa.accept_7_6_3_2_1_461 83 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 101 212 (accept_3_2 82 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 101 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 101 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 212 (accept_3_2 79 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 212
  (Polychromatic418967fa.accept_17_9_16_8_1_2721 77 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 101 212 (accept_3_2 76 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 101 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 101 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 74 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 212 (accept_3_2 73 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 212 (Polychromatic418967fa.accept_13_7_10_4_1_919 72 101
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 71 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 212 (accept_3_2 70 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 212 (accept_3_2 67 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 212
  (Polychromatic418967fa.accept_8_1_5_4_1_388 65 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 212 (accept_3_2 64 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 212 (accept_3_2 61 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 212
  (Polychromatic418967fa.accept_10_9_1_2_1_522 59 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 212 (accept_3_2 58 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 212 (Polychromatic418967fa.accept_10_6_1_2_1_874 56 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 212 (accept_3_2 55 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 101 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 212
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 212 (accept_3_2 52 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 212 (accept_3_2 49 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 101 212 (accept_3_2 46 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 101 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 101 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 212 (accept_3_2 43 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 212
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 212 (accept_3_2 40 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 212 (accept_3_2 37 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 101 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 212
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 101 212 (accept_3_2 34 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 101 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 212 (Polychromatic418967fa.accept_13_6_10_4_1_957 32 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 212 (accept_3_2 31 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 101 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 212 (accept_3_2 28 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 212 (accept_3_2 25 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 212
  (Polychromatic418967fa.accept_10_3_1_2_1_521 23 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 212 (accept_3_2 22 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 212 (accept_3_2 19 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 212 (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 101 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 212
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 212 (accept_3_2 16 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 212 (accept_3_2 13 101 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 101 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 212
  (Polychromatic418967fa.accept_13_11_10_4_1_1565 11 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 212 (accept_3_2 10 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 101 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 212 (accept_3_2 7 101 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 6
  101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 212 (accept_3_2 4 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 101 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 212 (accept_3_2 1 101 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 212 (allA_of_3_0 100 100 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 212 (allA_succ_of_accept 98 99
  212 (Polychromatic418967fa.accept_15_8_9_2_1_1897 98 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 99 212 (accept_3_2 97 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 99 212 (Polychromatic418967fa.accept_17_11_14_8_1_2729 96 99 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 99 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 212 (accept_3_2 94 99 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 212 (Polychromatic418967fa.accept_18_3_9_14_1_2219
  93 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 212
  (Polychromatic418967fa.accept_14_8_1_2_1_965 92 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 212 (accept_3_2 91 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 212 (accept_3_2 88 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 87 99 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 212
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 86 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 212 (accept_3_2 85 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 212 (Polychromatic418967fa.accept_17_16_14_8_1_7608 84 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 212 (accept_3_2 82 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 212 (Polychromatic418967fa.accept_10_1_9_2_1_45 81 99 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 80 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 212 (accept_3_2 79 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 212 (accept_3_2 76 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 212 (Polychromatic418967fa.accept_13_10_8_4_1_3098 75 99 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 212
  (Polychromatic418967fa.accept_13_9_8_4_1_937 74 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 212 (accept_3_2 73 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 212 (Polychromatic418967fa.accept_16_8_3_4_1_3233 72 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 212 (accept_3_2 70 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 99 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 212
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 68 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 212 (accept_3_2 67 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 212 (accept_3_2 64 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 99 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 212
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 212 (accept_3_2 61 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 212 (Polychromatic418967fa.accept_16_12_3_4_1_4317 60 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 212 (accept_3_2 58 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 212 (Polychromatic418967fa.accept_10_7_9_2_1_1887 57 99 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 212
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 56 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 212 (accept_3_2 55 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 212 (accept_3_2 52 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 212 (Polychromatic418967fa.accept_10_1_9_2_1_45 51 99 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 212
  (Polychromatic418967fa.accept_13_11_8_4_1_3950 50 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 212 (accept_3_2 49 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 212 (accept_3_2 46 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 99 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 212
  (Polychromatic418967fa.accept_16_12_3_4_1_4317 44 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 212 (accept_3_2 43 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 212 (accept_3_2 40 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 99 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 212 (accept_3_2 37 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 212 (Polychromatic418967fa.accept_13_10_8_4_1_3098 36 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 212 (accept_3_2 34 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 212 (Polychromatic418967fa.accept_16_1_3_4_1_665 33 99 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 212
  (Polychromatic418967fa.accept_19_13_4_3_1_2945 32 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 212 (accept_3_2 31 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 212 (accept_3_2 28 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 99 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 212
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 212 (accept_3_2 25 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 212 (accept_3_2 22 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 212 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 99 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 212
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 212 (accept_3_2 19 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 212 (accept_3_2 16 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 99 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 212
  (Polychromatic418967fa.accept_27_14_18_23_1_12553 14 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 99 212 (accept_3_2 13 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 99 212 (Polychromatic418967fa.accept_13_12_8_4_1_3099 12 99 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 212 (accept_3_2 10 99 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 212 (Polychromatic418967fa.accept_13_9_8_4_1_937 9
  99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 212
  (Polychromatic418967fa.accept_14_8_1_2_1_965 8 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 212 (accept_3_2 7 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  212 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 99 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 212 (accept_3_2 4 99 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 99 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 212 (Polychromatic418967fa.accept_20_2_19_12_1_2500
  2 99 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 212 (accept_3_2 1 99
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  212 (allA_succ_of_accept 97 98 212 (accept_3_2 97 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96
  98 212 2 48 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 98 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 95 98 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 98 212 2 47 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 98 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 93
  98 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 98 212 2 46 49 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 98 212 (accept_3_2 91
  98 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 98 212 2 45 49 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 98 212
  (Polychromatic418967fa.accept_12_5_2_8_1_172 89 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 98 212 2 44 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 98 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 87 98 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 98 212 2 43 49 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 98 212 (accept_3_2 85 98 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98 212 2 42 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 98 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 83
  98 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 98 212 2 41 49 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 98 212
  (Polychromatic418967fa.accept_13_3_7_4_1_435 81 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 98 212 2 40 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 98 212 (accept_3_2 79 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 98 212 2 39 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 98 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 98 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 98 212 2 38 49 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 98 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 75 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 98 212 2 37 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 98 212 (accept_3_2 73 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 98 212 2 36 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 98 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 98 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 98 212 2 35 49 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 98 212
  (Polychromatic418967fa.accept_9_6_8_5_1_837 69 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 98 212 2 34 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 98 212 (accept_3_2 67 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 98 212 2 33 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 98 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 98 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 98 212 2 32 49 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 98 212
  (Polychromatic418967fa.accept_13_11_7_4_1_1561 63 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 98 212 2 31 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 98 212 (accept_3_2 61 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 98 212 2 30 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 98 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 98 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 98 212 2 29 49 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 98 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 98 212 2 28 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 98 212 (accept_3_2 55 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 98 212 2 27 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 98 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 98 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 98 212 2 26 49 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 98 212
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 98 212 2 25 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 98 212 (accept_3_2 49 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 98 212 2 24 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 98 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 98 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 212 2 23 49 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 212
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 98 212 2 22 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 98 212 (accept_3_2 43 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 98 212 2 21 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 98 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 98 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 98 212 2 20 49 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 98 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 98 212 2 19 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 98 212 (accept_3_2 37 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 98 212 2 18 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 98 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 98 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 98 212 2 17 49 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 98 212
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 98 212 2 16 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 98 212 (accept_3_2 31 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 98 212 2 15 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 98 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 98 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 212 2 14 49 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 212
  (Polychromatic418967fa.accept_21_6_14_2_1_7980 27 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 212 2 13 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 98 212 (accept_3_2 25 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 98 212 2 12 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 98 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 98 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 98 212 2 11 49 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 98 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 98 212 2 10 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 98 212 (accept_3_2 19 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 98 212 2 9 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 98 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 98 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 212 2 8 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 15
  98 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 212 2 7 49 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 212 (accept_3_2 13
  98 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98 212 2 6 49 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 98 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 98 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 98 212 2 5 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 98 212 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 98 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 212 2 4 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 212 (accept_3_2 7 98 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 98 212 2 3 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 98 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 98 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 212 2 2 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 98
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 212 2 1 49 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 212 (accept_3_2 1 98
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  212 (allA_of_3_0 97 97 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 212 (allA_succ_of_accept 95 96 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 95 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 96 212 2 47 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 96 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 93 96 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 96 212 4 23 24 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 96 212 (accept_3_2 91 96 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 212 2 45 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 89
  96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 212 4 22 24 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 87 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 96 212 2 43 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 96 212 (accept_3_2 85 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 96 212 4 21 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 96 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 83 96 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 212 2 41 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 81
  96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 96 212 4 20 24 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 212 (accept_3_2 79
  96 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 212 2 39 48 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 212
  (Polychromatic418967fa.accept_13_12_5_4_1_3133 77 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 96 212 4 19 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 96 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 96 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 96 212 2 37 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 96 212 (accept_3_2 73 96 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 212 4 18 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 71 96 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 212 2 35 48 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 96 212
  (Polychromatic418967fa.accept_17_1_11_8_1_2725 69 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 96 212 4 17 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 96 212 (accept_3_2 67 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96
  212 2 33 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  65 96 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 96 212 4 16 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 96 212 (Polychromatic418967fa.accept_14_7_12_2_1_2502 63 96 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 212 2 31 48 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 212 (accept_3_2 61 96 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 212 4 15 24 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 96 212 2 29 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 96 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 96 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 96 212 4 14 24 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96 212 (accept_3_2 55 96 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 212 2 27 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 53
  96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 212 4 13 24 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 96 212
  (Polychromatic418967fa.accept_10_1_6_2_1_867 51 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 96 212 2 25 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 96 212 (accept_3_2 49 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 212 4 12 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 96 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 96 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 212 2 23 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 45
  96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 96 212 4 11 24 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 212 (accept_3_2 43
  96 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 212 2 21 48 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 212
  (Polychromatic418967fa.accept_10_1_6_2_1_867 41 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 96 212 4 10 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 96 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 96 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 212 2 19 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 212 (accept_3_2 37 96 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 212 4 9 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 96 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 96 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 212 2 17 48 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 212
  (Polychromatic418967fa.accept_22_11_8_14_1_12552 33 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 96 212 4 8 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 96 212 (accept_3_2 31 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 212 2 15 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 96 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 96 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 212 4 7 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 212 (Polychromatic418967fa.accept_11_5_8_3_1_66 27
  96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 212 2 13 48 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 212 (accept_3_2 25
  96 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 212 4 6 24 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 212
  (Polychromatic418967fa.accept_13_10_5_4_1_3107 23 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 96 212 2 11 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 96 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 96 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 96 212 4 5 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 212 (accept_3_2 19 96 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 212 2 9 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 96 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 212 4 4 24 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 212
  (Polychromatic418967fa.accept_13_2_5_4_1_3926 15 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 96 212 2 7 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 96 212 (accept_3_2 13 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96
  212 4 3 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  96 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 96 212 2 5 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 96 212 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 96 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 96 212 4 2 24 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 212 (accept_3_2 7 96 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 212 2 3 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 212 (Polychromatic418967fa.accept_11_5_8_3_1_66 5 96 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 212 4 1 24 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 96 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 96 212 2 1 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 96 212 (accept_3_2 1 96 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 212
  (allA_succ_of_accept 94 95 212 (accept_3_2 94 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 212 (Polychromatic418967fa.accept_11_4_7_3_1_289 92 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 212 (accept_3_2 91 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 90 95 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 89 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 212 (accept_3_2 88 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 86 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 212 (accept_3_2 85 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 212 (Polychromatic418967fa.accept_22_18_7_14_1_11033 84 95 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 212
  (Polychromatic418967fa.accept_7_6_4_2_1_236 83 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 212 (accept_3_2 82 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 212 (Polychromatic418967fa.accept_17_12_10_8_1_5039 80 95 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 212 (accept_3_2 79 95 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 212 (Polychromatic418967fa.accept_10_8_5_2_1_881 78 95 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 212
  (Polychromatic418967fa.accept_10_7_5_2_1_880 77 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 212 (accept_3_2 76 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 74 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 212 (accept_3_2 73 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 212 (Polychromatic418967fa.accept_15_12_5_2_1_2786 72 95 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 212
  (Polychromatic418967fa.accept_15_11_5_2_1_520 71 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 212 (accept_3_2 70 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 212 (accept_3_2 67 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 212 (Polychromatic418967fa.accept_17_15_10_8_1_1708 66 95 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 212
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 65 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 212 (accept_3_2 64 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 212 (accept_3_2 61 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 212 (Polychromatic418967fa.accept_16_12_15_4_1_5422 60 95 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 212
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 212 (accept_3_2 58 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 212 (Polychromatic418967fa.accept_15_11_5_2_1_520 56 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 212 (accept_3_2 55 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 95 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 212
  (Polychromatic418967fa.accept_10_3_5_2_1_38 53 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 212 (accept_3_2 52 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 212 (accept_3_2 49 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 95 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 212 (accept_3_2 46 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 212 (Polychromatic418967fa.accept_15_14_5_2_1_4761 44 95 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 212 (accept_3_2 43 95 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 212 (Polychromatic418967fa.accept_15_12_5_2_1_2786 42 95
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 212
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 212 (accept_3_2 40 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 212 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 212 (accept_3_2 37 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 212 (Polychromatic418967fa.accept_17_2_10_8_1_7691 36 95 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 212
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 212 (accept_3_2 34 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 212 (Polychromatic418967fa.accept_11_10_7_3_1_3679 32 95 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 212 (accept_3_2 31 95 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 212 (Polychromatic418967fa.accept_16_14_15_4_1_3268 30 95
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 212
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 212 (accept_3_2 28 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 212 (accept_3_2 25 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 212 (Polychromatic418967fa.accept_16_8_15_4_1_5402 24 95 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 212
  (Polychromatic418967fa.accept_10_3_5_2_1_38 23 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 212 (accept_3_2 22 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 212 (accept_3_2 19 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 212 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 95 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 212
  (Polychromatic418967fa.accept_10_7_5_2_1_880 17 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 212 (accept_3_2 16 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 212 (accept_3_2 13 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 95 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 212
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 212 (accept_3_2 10 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 212 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 212 (accept_3_2 7 95 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 95 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 212 (accept_3_2 4 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 95 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 212 (accept_3_2 1 95 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 212
  (allA_of_3_0 94 94 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 212 (allA_succ_of_accept 92 93 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 92 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 212 (accept_3_2 91 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 212 (accept_3_2 88 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 87 93 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 212
  (Polychromatic418967fa.accept_16_6_13_4_1_643 86 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 212 (accept_3_2 85 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 212 (Polychromatic418967fa.accept_13_6_2_4_1_923 84 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 212 (accept_3_2 82 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 81 93 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 80 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 212 (accept_3_2 79 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 212 (accept_3_2 76 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 212 (Polychromatic418967fa.accept_10_5_3_2_1_899 75 93 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 74 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 212 (accept_3_2 73 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 212 (Polychromatic418967fa.accept_15_12_3_2_1_2756 72 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 212 (accept_3_2 70 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 93 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 212
  (Polychromatic418967fa.accept_23_22_1_5_1_10875 68 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 212 (accept_3_2 67 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 212 (accept_3_2 64 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 212 (Polychromatic418967fa.accept_11_8_5_3_1_694 63 93 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 62 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 212 (accept_3_2 61 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 212 (accept_3_2 58 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 93 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 212 (accept_3_2 55 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 212 (accept_3_2 52 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 93 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 212
  (Polychromatic418967fa.accept_13_11_2_4_1_1590 50 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 212 (accept_3_2 49 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 212 (Polychromatic418967fa.accept_18_12_3_14_1_5919 48 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 212 (accept_3_2 46 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 212 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 93 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 212 (accept_3_2 43 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 212 (accept_3_2 40 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 212 (Polychromatic418967fa.accept_14_11_9_2_1_6382 39 93 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 212 (accept_3_2 37 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 212 (Polychromatic418967fa.accept_21_15_9_2_1_7973 36 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 212 (accept_3_2 34 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 93 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 212
  (Polychromatic418967fa.accept_13_6_2_4_1_923 32 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 212 (accept_3_2 31 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 212 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 212 (accept_3_2 28 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 212 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 93 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 212 (accept_3_2 25 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 212 (accept_3_2 22 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 212 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 93 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 212 (accept_3_2 19 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 212 (accept_3_2 16 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 93 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 212
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 212 (accept_3_2 13 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 212 (Polychromatic418967fa.accept_13_12_2_4_1_3131 12 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 212 (accept_3_2 10 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 93 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 212 (accept_3_2 7 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  212 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 93 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 212 (accept_3_2 4 93 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 212 (Polychromatic418967fa.accept_20_3_13_12_1_5218 3 93 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 93
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 212 (accept_3_2 1 93 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 212
  (allA_succ_of_accept 91 92 212 (accept_3_2 91 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 92
  212 2 45 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  89 92 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 89 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 92 212 4 22 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 92 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 87 92 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 92 212 2 43 46 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 92 212 (accept_3_2 85 92 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 92 212 4 21 23 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 92 212
  (Polychromatic418967fa.accept_7_6_1_2_1_230 83 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 92 212 2 41 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 92 212 (Polychromatic418967fa.accept_13_3_1_4_1_945 81 92 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 92 212 4 20 23 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 92 212 (accept_3_2 79 92 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 92 212 2 39 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 92 212 (Polychromatic418967fa.accept_16_13_12_4_1_4323
  77 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 92 212 4 19 23 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 92 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 75 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 92 212 2 37 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 92 212 (accept_3_2 73 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 92 212 4 18 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 92 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 92 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 92 212 2 35 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 92 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 69
  92 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 92 212 4 17 23 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 92 212 (accept_3_2 67
  92 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 92 212 2 33 46 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 92 212
  (Polychromatic418967fa.accept_16_1_12_4_1_695 65 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 92 212 4 16 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 92 212 (Polychromatic418967fa.accept_16_15_12_4_1_4324 63 92 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 92 212 2 31 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 92 212 (accept_3_2 61 92 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92 212 4 15 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 92 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 92 212 2 29 46 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 92 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 57 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 92 212 4 14 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 92 212 (accept_3_2 55 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92
  212 2 27 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 92 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 92 212 4 13 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 92 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 92 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 92 212 2 25 46 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 92 212 (accept_3_2 49 92 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92 212 4 12 23 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 92 212
  (Polychromatic418967fa.accept_16_15_12_4_1_4324 47 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 92 212 2 23 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 92 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 92 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 212 4 11 23 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 212 (accept_3_2 43 92 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 212 2 21 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 41
  92 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 92 212 4 10 23 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 92 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 92 212 2 19 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 92 212 (accept_3_2 37 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 92 212 4 9 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 92 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 92 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 212 2 17 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 33
  92 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 92 212 4 8 23 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 92 212 (accept_3_2 31
  92 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92 212 2 15 46 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 92 212
  (Polychromatic418967fa.accept_11_7_4_3_1_302 29 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 92 212 4 7 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 92 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 92 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 212 2 13 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 212 (accept_3_2 25 92 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 212 4 6 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 92 212 (Polychromatic418967fa.accept_13_10_1_4_1_3103 23 92 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 212 2 11 46 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 212 4 5 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 92 212 (accept_3_2 19 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92
  212 2 9 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  92 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 92 212 4 4 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 92 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 92 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 212 2 7 46 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 212 (accept_3_2 13 92 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 212 4 3 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 92 212 (Polychromatic418967fa.accept_16_11_12_4_1_3195 11 92
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 212 2 5 46 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 212
  (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 92 212 4 2 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 92 212 (accept_3_2 7 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 212
  2 3 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92
  212 (Polychromatic418967fa.accept_13_5_1_4_1_3966 5 92 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 92 212 4 1 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 92 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 92 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 212 2 1 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 212 (accept_3_2 1 92 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 92
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 212
  (allA_of_3_0 91 91 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 212 (allA_succ_of_accept 89 90 212
  (Polychromatic418967fa.accept_11_1_2_3_1_688 89 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 90 212 2 44 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 90 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 90 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 90 212 2 43 45 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 90 212 (accept_3_2 85 90 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 212 2 42 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 212 (Polychromatic418967fa.accept_13_5_12_4_1_449
  83 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 212 2 41 45 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 90 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 81 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 90 212 2 40 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 90 212 (accept_3_2 79 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 90 212 2 39 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 90 212 (Polychromatic418967fa.accept_21_14_6_2_1_4793 77 90 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 212 2 38 45 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 90 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 75 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 90 212 2 37 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 90 212 (accept_3_2 73 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 212 2 36 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 90 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 90 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 212 2 35 45 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 90 212 2 34 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 90 212 (accept_3_2 67 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 212 2 33 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 90 212 (Polychromatic418967fa.accept_19_8_14_3_1_4151 65 90 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 212 2 32 45 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 90 212 2 31 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 90 212 (accept_3_2 61 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 212 2 30 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 90 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 90 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 212 2 29 45 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 90 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 90 212 2 28 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 90 212 (accept_3_2 55 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 212 2 27 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 90 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 90 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 212 2 26 45 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 212 2 25 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 90 212 (accept_3_2 49 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 212 2 24 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 90 212 (Polychromatic418967fa.accept_13_8_12_4_1_4858 47 90 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 212 2 23 45 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 90 212 2 22 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 90 212 (accept_3_2 43 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 212 2 21 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 90 212 (Polychromatic418967fa.accept_13_2_12_4_1_943 41 90 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 212 2 20 45 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 90 212 2 19 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 90 212 (accept_3_2 37 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 212 2 18 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 90 212 (Polychromatic418967fa.accept_19_16_14_3_1_11194 35 90 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 212 2 17 45 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 212 2 16 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 90 212 (accept_3_2 31 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 212 2 15 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 90 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 90 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 212 2 14 45 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 90 212 2 13 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 90 212 (accept_3_2 25 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 212 2 12 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 90 212 (Polychromatic418967fa.accept_11_1_2_3_1_688 23 90 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 212 2 11 45 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 212 2 10 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 90 212 (accept_3_2 19 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 212 2 9 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 90 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 212 2 8 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  90 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 212 2 7 45 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 212 (accept_3_2 13
  90 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 212 2 6 45 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 90 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 90 212 2 5 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 90 212 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 90 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 212 2 4 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 212 (accept_3_2 7 90 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 90 212 2 3 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 90 212 (Polychromatic418967fa.accept_13_5_12_4_1_449 5 90 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 212 2 2 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 90
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 212 2 1 45 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 212 (accept_3_2 1 90
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 212
  (allA_succ_of_accept 88 89 212 (accept_3_2 88 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 86 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 212 (accept_3_2 85 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 89 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 83 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 212 (accept_3_2 82 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 80 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 212 (accept_3_2 79 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 89 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 212
  (Polychromatic418967fa.accept_8_5_1_4_1_628 77 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 212 (accept_3_2 76 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 74 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 212 (accept_3_2 73 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 212 (Polychromatic418967fa.accept_13_7_11_4_1_2247 72 89 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 212
  (Polychromatic418967fa.accept_10_1_9_2_1_45 71 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 212 (accept_3_2 70 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 212 (Polychromatic418967fa.accept_11_2_1_3_1_683 68 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 212 (accept_3_2 67 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 89 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 212 (accept_3_2 64 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 212 (accept_3_2 61 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 89 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 212 (accept_3_2 58 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 212 (accept_3_2 55 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 212 (Polychromatic418967fa.accept_13_2_11_4_1_445 54 89 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 212 (accept_3_2 52 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 212 (accept_3_2 49 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 89 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 212 (accept_3_2 46 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 212 (Polychromatic418967fa.accept_16_12_9_4_1_4345 44 89 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 212 (accept_3_2 43 89 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 89 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 212
  (Polychromatic418967fa.accept_10_1_9_2_1_45 41 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 212 (accept_3_2 40 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 212 (accept_3_2 37 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 212 (Polychromatic418967fa.accept_13_10_11_4_1_2248 36 89 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 212
  (Polychromatic418967fa.accept_11_2_1_3_1_683 35 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 212 (accept_3_2 34 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 212 (accept_3_2 31 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 89 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 212
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 212 (accept_3_2 28 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 212 (accept_3_2 25 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 89 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 212
  (Polychromatic418967fa.accept_13_10_11_4_1_2248 23 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 212 (accept_3_2 22 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 212 (accept_3_2 19 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 89 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 212 (accept_3_2 16 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 212 (accept_3_2 13 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 89 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 212 (accept_3_2 10 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 212 (Polychromatic418967fa.accept_13_8_11_4_1_1553 8 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 212 (accept_3_2 7 89 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 89 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 212
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 212 (accept_3_2 4 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 89 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 89 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 212 (accept_3_2 1 89 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 212 (allA_of_3_0 88 88 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 212
  (allA_succ_of_accept 86 87 212 (Polychromatic418967fa.accept_13_8_9_4_1_1552 86 87 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 212 (accept_3_2 85 87 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 83
  87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 212 (accept_3_2 82 87
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 212
  (Polychromatic418967fa.accept_15_6_12_2_1_2803 81 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 80 87 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 212 (accept_3_2 79 87 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 77
  87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 212 (accept_3_2 76 87
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 75 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 74 87 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 212 (accept_3_2 73 87 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 212 (Polychromatic418967fa.accept_13_7_9_4_1_918 72 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 71
  87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 212 (accept_3_2 70 87
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 212
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 87 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 212 (accept_3_2 67 87 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 65
  87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 212 (accept_3_2 64 87
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 212
  (Polychromatic418967fa.accept_15_3_12_2_1_507 63 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 87 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 212 (accept_3_2 61 87 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 212 (Polychromatic418967fa.accept_13_8_9_4_1_1552 60 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 59
  87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 212 (accept_3_2 58 87
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 212 (Polychromatic418967fa.accept_7_1_3_2_1_13
  57 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 212 (accept_3_2 55 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 212 (accept_3_2 52 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 87 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 212 (accept_3_2 49 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 212 (accept_3_2 46 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 212 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 87 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 212 (accept_3_2 43 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 212 (accept_3_2 40 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 87 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 212 (accept_3_2 37 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 212 (accept_3_2 34 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 87 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 212
  (Polychromatic418967fa.accept_13_6_9_4_1_2288 32 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 212 (accept_3_2 31 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 212 (accept_3_2 28 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 87 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 212 (accept_3_2 25 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 212 (accept_3_2 22 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 87 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 212
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 212 (accept_3_2 19 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 212 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 212 (accept_3_2 16 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 87 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 212
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 212 (accept_3_2 13 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 212 (accept_3_2 10 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 212 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 87 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 212 (accept_3_2 7 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  212 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 87 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 212 (accept_3_2 4 87 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 87 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  87 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 212 (accept_3_2 1 87 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 212
  (allA_succ_of_accept 85 86 212 (accept_3_2 85 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 86
  212 2 42 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  83 86 212 (Polychromatic418967fa.accept_11_6_9_3_1_1103 83 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 86 212 2 41 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 86 212 (Polychromatic418967fa.accept_10_1_6_2_1_867 81 86 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 86 212 2 40 43 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 86 212 (accept_3_2 79 86 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86 212 2 39 43 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 86 212
  (Polychromatic418967fa.accept_12_5_2_8_1_172 77 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 86 212 2 38 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 86 212 (Polychromatic418967fa.accept_13_10_8_4_1_3098 75 86 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 212 2 37 43 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 212 (accept_3_2 73 86 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 212 2 36 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 212 (Polychromatic418967fa.accept_10_1_6_2_1_867 71
  86 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 86 212 2 35 43 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 86 212
  (Polychromatic418967fa.accept_15_9_11_2_1_1882 69 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 86 212 2 34 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 86 212 (accept_3_2 67 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 86 212 2 33 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 86 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 86 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 86 212 2 32 43 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 86 212
  (Polychromatic418967fa.accept_13_11_8_4_1_3950 63 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 86 212 2 31 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 86 212 (accept_3_2 61 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 86 212 2 30 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 86 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 86 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 86 212 2 29 43 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 86 212
  (Polychromatic418967fa.accept_20_17_6_12_1_8185 57 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 86 212 2 28 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 86 212 (accept_3_2 55 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 86 212 2 27 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 86 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 86 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 212 2 26 43 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 212
  (Polychromatic418967fa.accept_10_1_6_2_1_867 51 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 212 2 25 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 86 212 (accept_3_2 49 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 86 212 2 24 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 86 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 86 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 86 212 2 23 43 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 86 212
  (Polychromatic418967fa.accept_16_13_6_4_1_3277 45 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 86 212 2 22 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 86 212 (accept_3_2 43 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 86 212 2 21 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 86 212 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 86 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 212 2 20 43 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 212
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 39 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 86 212 2 19 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 86 212 (accept_3_2 37 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 86 212 2 18 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 86 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 86 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 212 2 17 43 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 212
  (Polychromatic418967fa.accept_22_11_20_14_1_12551 33 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 86 212 2 16 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 86 212 (accept_3_2 31 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 86 212 2 15 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 86 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 86 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 212 2 14 43 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 212
  (Polychromatic418967fa.accept_16_11_6_4_1_2228 27 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 212 2 13 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 86 212 (accept_3_2 25 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 86 212 2 12 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 86 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 86 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 86 212 2 11 43 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 212
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 86 212 2 10 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 86 212 (accept_3_2 19 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 86 212 2 9 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 86 212 (Polychromatic418967fa.accept_11_6_9_3_1_1103 17 86 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 212 2 8 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 212
  (Polychromatic418967fa.accept_19_15_10_3_1_12550 15 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 86 212 2 7 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 86 212 (accept_3_2 13 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 86 212 2 6 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 86 212 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 86 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 86 212 2 5 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 86 212 (Polychromatic418967fa.accept_13_9_8_4_1_937 9
  86 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 212 2 4 43 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 212 (accept_3_2 7 86
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 212 2 3 43 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 86 212
  (Polychromatic418967fa.accept_12_5_2_8_1_172 5 86 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 86 212 2 2 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 86 212 (Polychromatic418967fa.accept_16_3_6_4_1_679 3 86 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 212 2 1 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 212 (accept_3_2 1 86 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 86 212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 85 212 (allA_of_3_0 85 85 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 212
  (allA_succ_of_accept 83 84 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 83 84 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 84 212 2 41 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 84 212 (Polychromatic418967fa.accept_11_4_7_3_1_289 81
  84 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 84 212 4 20 21 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 212 (accept_3_2 79
  84 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 212 2 39 42 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 212
  (Polychromatic418967fa.accept_10_7_4_2_1_903 77 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 84 212 4 19 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 84 212 (Polychromatic418967fa.accept_13_10_6_4_1_1583 75 84 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 84 212 2 37 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 84 212 (accept_3_2 73 84 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 212 4 18 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 84 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 212 2 35 42 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 212
  (Polychromatic418967fa.accept_9_6_3_5_1_240 69 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 84 212 4 17 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 84 212 (accept_3_2 67 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84
  212 2 33 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  65 84 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 84 212 4 16 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 84 212 (Polychromatic418967fa.accept_13_11_6_4_1_3121 63 84 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 212 2 31 42 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 212 (accept_3_2 61 84 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 212 4 15 21 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 212
  (Polychromatic418967fa.accept_11_4_7_3_1_289 59 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 84 212 2 29 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 84 212 (Polychromatic418967fa.accept_10_7_4_2_1_903 57 84 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 84 212 4 14 21 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 212 (accept_3_2 55 84 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 212 2 27 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 53
  84 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 212 4 13 21 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 84 212
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 84 212 2 25 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 84 212 (accept_3_2 49 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 212 4 12 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 84 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 84 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 212 2 23 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 84 212
  (Polychromatic418967fa.accept_22_1_18_14_1_12549 45 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 84 212 4 11 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 84 212 (accept_3_2 43 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 84 212 2 21 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 84 212 (Polychromatic418967fa.accept_13_2_6_4_1_1593 41 84 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 212 4 10 21 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 212
  (Polychromatic418967fa.accept_18_3_12_14_1_2232 39 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 84 212 2 19 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 84 212 (accept_3_2 37 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 212 4 9 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 84 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 84 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 212 2 17 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 33
  84 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 212 4 8 21 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 212 (accept_3_2 31
  84 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 212 2 15 42 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 212 4 7 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 84 212 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 84 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 212 2 13 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 212 (accept_3_2 25 84 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 212 4 6 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 84 212 (Polychromatic418967fa.accept_13_10_6_4_1_1583 23 84 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 212 2 11 42 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 212
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 212 4 5 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 212 (accept_3_2 19 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84
  212 2 9 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  84 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 84 212 4 4 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 84 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 84 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 212 2 7 42 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 212 (accept_3_2 13 84 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 212 4 3 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 84 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 212 2 5 42 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 212
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 212 4 2 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 212 (accept_3_2 7 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 212
  2 3 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84
  212 (Polychromatic418967fa.accept_13_5_6_4_1_1582 5 84 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 84 212 4 1 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 84 212 (Polychromatic418967fa.accept_18_3_12_14_1_2232 3 84 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 212 2 1 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 212 (accept_3_2 1 84 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 84
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 212
  (allA_succ_of_accept 82 83 212 (accept_3_2 82 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 212 (accept_3_2 79 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 83 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 212
  (Polychromatic418967fa.accept_13_12_5_4_1_3133 77 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 212 (accept_3_2 76 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 212 (accept_3_2 73 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 212 (Polychromatic418967fa.accept_16_8_3_4_1_3233 72 83 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 212 (accept_3_2 70 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 212 (Polychromatic418967fa.accept_21_5_20_2_1_7948 68 83 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 212 (accept_3_2 67 83 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 83 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 212
  (Polychromatic418967fa.accept_10_5_3_2_1_899 65 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 212 (accept_3_2 64 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 212 (accept_3_2 61 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 83 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 212 (accept_3_2 58 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 212 (Polychromatic418967fa.accept_16_8_3_4_1_3233 56 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 212 (accept_3_2 55 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 212 (Polychromatic418967fa.accept_13_2_5_4_1_3926 54 83 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 212 (accept_3_2 52 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 212 (accept_3_2 49 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 83 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 212
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 212 (accept_3_2 46 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 212 (accept_3_2 43 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 83 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 212
  (Polychromatic418967fa.accept_10_1_3_2_1_220 41 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 212 (accept_3_2 40 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 212 (accept_3_2 37 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 83 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 212
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 212 (accept_3_2 34 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 212 (accept_3_2 31 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 83 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 212 (accept_3_2 28 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 212 (accept_3_2 25 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 83 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 212
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 212 (accept_3_2 22 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 212 (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 212 (accept_3_2 19 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 83 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 212 (accept_3_2 16 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 212 (accept_3_2 13 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 83 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 212 (accept_3_2 10 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 212 (accept_3_2 7 83 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 83 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 212
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 212 (accept_3_2 4 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 83 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 212 (accept_3_2 1 83 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 212 (allA_of_3_0 82 82 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 212
  (allA_succ_of_accept 80 81 212 (Polychromatic418967fa.accept_24_8_9_20_1_7244 80 81 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 212 (accept_3_2 79 81 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 81 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 77
  81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 212 (accept_3_2 76 81
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 212 (Polychromatic418967fa.accept_19_17_5_3_1_5455 74 81 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 212 (accept_3_2 73 81 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 212 (Polychromatic418967fa.accept_13_7_3_4_1_459 72 81 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 71
  81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 212 (accept_3_2 70 81
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 212
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 81 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 212 (accept_3_2 67 81 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 212 (Polychromatic418967fa.accept_10_6_1_2_1_874 66 81 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 65
  81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 212 (accept_3_2 64 81
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 212
  (Polychromatic418967fa.accept_10_3_1_2_1_521 63 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 81 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 212 (accept_3_2 61 81 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 212 (Polychromatic418967fa.accept_16_12_1_4_1_5403 60 81 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 212 (accept_3_2 58 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  81 212 (Polychromatic418967fa.accept_15_12_6_2_1_2760 57 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 81 212 (Polychromatic418967fa.accept_10_6_1_2_1_874 56 81 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 212 (accept_3_2 55 81 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 81 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 212 (accept_3_2 52 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 212 (Polychromatic418967fa.accept_11_7_4_3_1_302 51 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 212 (Polychromatic418967fa.accept_22_6_15_14_1_4436 50 81 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 212 (accept_3_2 49 81 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 81 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 212 (accept_3_2 46 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 212 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 212 (Polychromatic418967fa.accept_16_12_1_4_1_5403 44 81 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 212 (accept_3_2 43 81 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 81 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 212 (accept_3_2 40 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 212 (Polychromatic418967fa.accept_10_9_1_2_1_522 39 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 212 (Polychromatic418967fa.accept_13_12_3_4_1_928 38 81 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 212 (accept_3_2 37 81 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 212 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 81 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 212 (accept_3_2 34 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 212 (Polychromatic418967fa.accept_17_15_13_8_1_7603 32 81 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 212 (accept_3_2 31 81 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 81 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 212 (accept_3_2 28 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 81 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 212 (accept_3_2 25 81 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 212 (Polychromatic418967fa.accept_16_8_1_4_1_6622 24 81 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 212 (accept_3_2 22 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 212 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 81 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 212 (accept_3_2 19 81 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 212 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 81 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 212 (accept_3_2 16 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 212 (Polychromatic418967fa.accept_17_15_13_8_1_7603 15 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 212 (Polychromatic418967fa.accept_13_1_3_4_1_925 14 81 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 212 (accept_3_2 13 81 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 81 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 212 (accept_3_2 10 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 212 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 212 (Polychromatic418967fa.accept_15_8_6_2_1_1128 8 81 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 212 (accept_3_2 7 81 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 81 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 212 (accept_3_2 4 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  212 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 81 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 212 (Polychromatic418967fa.accept_19_2_5_3_1_5536 2 81 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 212 (accept_3_2 1 81 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 212 (allA_succ_of_accept 79 80 212 (accept_3_2 79 80 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 80 212 2 39 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 80 212 (Polychromatic418967fa.accept_13_12_2_4_1_3131 77 80 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 80 212 4 19 20 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 80 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 75 80 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 80 212 2 37 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 80 212 (accept_3_2 73 80 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 80 212 4 18 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 80 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 80 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 80 212 2 35 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 80 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 69
  80 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 212 4 17 20 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 212 (accept_3_2 67
  80 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 212 2 33 40 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 80 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 80 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 80 212 4 16 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 80 212 (Polychromatic418967fa.accept_13_11_2_4_1_1590 63 80 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 80 212 2 31 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 80 212 (accept_3_2 61 80 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80 212 4 15 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 80 212 (Polychromatic418967fa.accept_15_14_5_2_1_4761 59 80 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 212 2 29 40 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 80 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 80 212 4 14 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 80 212 (accept_3_2 55 80 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80
  212 2 27 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 80 212 (Polychromatic418967fa.accept_21_11_17_2_1_4749 53 80 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 80 212 4 13 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 80 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 80 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 212 2 25 40 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 212 (accept_3_2 49 80 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 212 4 12 20 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 80 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 80 212 2 23 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 80 212 (Polychromatic418967fa.accept_13_6_2_4_1_923 45 80 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 80 212 4 11 20 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 80 212 (accept_3_2 43 80 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80 212 2 21 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 80 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 41
  80 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 80 212 4 10 20 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 80 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 80 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 80 212 2 19 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 80 212 (accept_3_2 37 80 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 80 212 4 9 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 80 212 (Polychromatic418967fa.accept_19_16_4_3_1_2946 35 80 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 212 2 17 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 33
  80 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 80 212 4 8 20 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 80 212 (accept_3_2 31
  80 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 212 2 15 40 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 80 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 80 212 4 7 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 80 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 80 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 212 2 13 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 212 (accept_3_2 25 80 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 212 4 6 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 80 212 (Polychromatic418967fa.accept_18_5_8_14_1_1282 23 80 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 212 2 11 40 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 80 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 212 4 5 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 212 (accept_3_2 19 80 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  212 2 9 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 212 (Polychromatic418967fa.accept_23_17_11_5_1_9195 17 80 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 212 4 4 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 80 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 212 2 7 40 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 212 (accept_3_2 13 80 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 212 4 3 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 80 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 80 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 212 2 5 40 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 212
  (Polychromatic418967fa.accept_21_9_17_2_1_9537 9 80 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 212 4 2 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 212 (accept_3_2 7 80 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 212
  2 3 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80
  212 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 80 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 80 212 4 1 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 80 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 80 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 212 2 1 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 212 (accept_3_2 1 80 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 79 212 (allA_of_3_0 79 79 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 212
  (allA_succ_of_accept 77 78 212 (Polychromatic418967fa.accept_19_1_2_3_1_6995 77 78 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78 212 2 38 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 78 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 75
  78 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 78 212 2 37 39 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 212 (accept_3_2 73
  78 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 212 2 36 39 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 78 212 2 35 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 78 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 78 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 78 212 2 34 39 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 78 212 (accept_3_2 67 78 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 212 2 33 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 65
  78 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 212 2 32 39 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 78 212 2 31 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 78 212 (accept_3_2 61 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 212 2 30 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 78 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 78 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 212 2 29 39 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 78 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 57 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 78 212 2 28 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 78 212 (accept_3_2 55 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 212 2 27 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 78 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 78 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 212 2 26 39 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 78 212 2 25 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 78 212 (accept_3_2 49 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 212 2 24 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 78 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 78 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 212 2 23 39 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 78 212 2 22 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 78 212 (accept_3_2 43 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 212 2 21 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 78 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 78 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 212 2 20 39 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 78 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 78 212 2 19 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 78 212 (accept_3_2 37 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 212 2 18 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 78 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 78 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 212 2 17 39 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 212 2 16 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 78 212 (accept_3_2 31 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 212 2 15 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 78 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 78 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 212 2 14 39 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 212
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 78 212 2 13 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 78 212 (accept_3_2 25 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 212 2 12 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 78 212 (Polychromatic418967fa.accept_16_7_14_4_1_1362 23 78 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 212 2 11 39 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 212 2 10 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 78 212 (accept_3_2 19 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 212 2 9 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 78 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 212 2 8 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 15
  78 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 212 2 7 39 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 212 (accept_3_2 13
  78 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 212 2 6 39 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 78 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 78 212 2 5 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 78 212 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 78 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 212 2 4 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 212 (accept_3_2 7 78 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 78 212 2 3 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 78 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 78 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 212 2 2 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 78
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 212 2 1 39 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 212 (accept_3_2 1 78
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 212
  (allA_succ_of_accept 76 77 212 (accept_3_2 76 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 74 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 212 (accept_3_2 73 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 212 (Polychromatic418967fa.accept_13_7_12_4_1_450 72 77 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 212
  (Polychromatic418967fa.accept_16_7_13_4_1_1348 71 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 212 (accept_3_2 70 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 212 (Polychromatic418967fa.accept_13_3_12_4_1_110 68 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 212 (accept_3_2 67 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 212 (Polychromatic418967fa.accept_20_6_17_12_1_8210 66 77 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 212
  (Polychromatic418967fa.accept_8_1_5_4_1_388 65 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 212 (accept_3_2 64 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 212 (accept_3_2 61 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 212 (Polychromatic418967fa.accept_13_8_12_4_1_4858 60 77 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 212
  (Polychromatic418967fa.accept_10_9_7_2_1_887 59 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 212 (accept_3_2 58 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 212 (Polychromatic418967fa.accept_16_8_13_4_1_3258 56 77 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 212 (accept_3_2 55 77 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 77 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 212
  (Polychromatic418967fa.accept_21_11_14_2_1_6371 53 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 212 (accept_3_2 52 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 212 (accept_3_2 49 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 212 (Polychromatic418967fa.accept_19_10_1_3_1_12548 48 77 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 212
  (Polychromatic418967fa.accept_13_8_12_4_1_4858 47 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 212 (accept_3_2 46 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 212 (accept_3_2 43 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 212 (Polychromatic418967fa.accept_13_3_12_4_1_110 42 77 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 212
  (Polychromatic418967fa.accept_8_1_5_4_1_388 41 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 212 (accept_3_2 40 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 212 (accept_3_2 37 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 212 (Polychromatic418967fa.accept_19_17_1_3_1_4160 36 77 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 212
  (Polychromatic418967fa.accept_10_5_7_2_1_516 35 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 212 (accept_3_2 34 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 212 (Polychromatic418967fa.accept_21_11_14_2_1_6371 32 77 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 212 (accept_3_2 31 77 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 212 (Polychromatic418967fa.accept_19_11_1_3_1_5555 30 77
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 212
  (Polychromatic418967fa.accept_10_9_7_2_1_887 29 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 212 (accept_3_2 28 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 212 (accept_3_2 25 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 77 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 212
  (Polychromatic418967fa.accept_14_9_7_2_1_2483 23 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 212 (accept_3_2 22 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 212 (Polychromatic418967fa.accept_13_7_12_4_1_450 20 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 212 (accept_3_2 19 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 212 (Polychromatic418967fa.accept_13_5_12_4_1_449 18 77 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 212
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 212 (accept_3_2 16 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 212 (accept_3_2 13 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 212 (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 77 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 212
  (Polychromatic418967fa.accept_13_11_12_4_1_3945 11 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 212 (accept_3_2 10 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 212 (Polychromatic418967fa.accept_13_8_12_4_1_4858 8 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 212 (accept_3_2 7 77 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 212 (Polychromatic418967fa.accept_16_6_13_4_1_643 6 77 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 212
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 212 (accept_3_2 4 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 77 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 77 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 212 (accept_3_2 1 77 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 212 (allA_of_3_0 76 76 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 212 (allA_succ_of_accept 74 75
  212 (Polychromatic418967fa.accept_7_4_5_2_1_243 74 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 212 (accept_3_2 73 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 212 (Polychromatic418967fa.accept_11_6_9_3_1_1103 72 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 212 (accept_3_2 70 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 75 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 212
  (Polychromatic418967fa.accept_10_8_5_2_1_881 68 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 212 (accept_3_2 67 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 212 (accept_3_2 64 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 75 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 62 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 212 (accept_3_2 61 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 212 (accept_3_2 58 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 212 (Polychromatic418967fa.accept_10_7_5_2_1_880 57 75 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 212 (accept_3_2 55 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 212 (accept_3_2 52 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 75 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 212
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 50 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 212 (accept_3_2 49 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 212 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 212 (accept_3_2 46 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 75 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 212 (accept_3_2 43 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 212 (accept_3_2 40 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 75 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 212 (accept_3_2 37 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 212 (Polychromatic418967fa.accept_27_9_21_23_1_12547 36 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 212 (accept_3_2 34 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 75 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 212 (accept_3_2 31 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 212 (accept_3_2 28 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 212 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 75 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 212 (accept_3_2 25 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 212 (accept_3_2 22 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 212 (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 75 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 212 (accept_3_2 19 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 212 (accept_3_2 16 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 75 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 212
  (Polychromatic418967fa.accept_13_1_10_4_1_954 14 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 212 (accept_3_2 13 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 212 (Polychromatic418967fa.accept_16_12_11_4_1_1359 12 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 212 (accept_3_2 10 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 212 (Polychromatic418967fa.accept_16_9_11_4_1_3194 9 75 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 212 (accept_3_2 7 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  212 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 75 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 75 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 212 (accept_3_2 4 75 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 75 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 75
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 212 (accept_3_2 1 75 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 212 (allA_succ_of_accept
  73 74 212 (accept_3_2 73 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 212 2 36 37 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 212
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 212 2 35 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 74 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 74 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 212 2 34 37 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 212 (accept_3_2 67 74 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 212 2 33 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 65
  74 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 212 2 32 37 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 212
  (Polychromatic418967fa.accept_15_3_14_2_1_1888 63 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 74 212 2 31 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 74 212 (accept_3_2 61 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 74 212 2 30 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 74 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 74 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 74 212 2 29 37 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 74 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 57 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 74 212 2 28 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 74 212 (accept_3_2 55 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 74 212 2 27 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 74 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 74 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 74 212 2 26 37 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 74 212
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 74 212 2 25 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 74 212 (accept_3_2 49 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 74 212 2 24 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 74 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 74 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 212 2 23 37 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 212
  (Polychromatic418967fa.accept_13_6_9_4_1_2288 45 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 212 2 22 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 74 212 (accept_3_2 43 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 74 212 2 21 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 74 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 74 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 212 2 20 37 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 212 2 19 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 74 212 (accept_3_2 37 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 74 212 2 18 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 74 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 74 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 212 2 17 37 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 74 212 2 16 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 74 212 (accept_3_2 31 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 74 212 2 15 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 74 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 74 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 212 2 14 37 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 212
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 212 2 13 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 74 212 (accept_3_2 25 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 74 212 2 12 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 74 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 74 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 212 2 11 37 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 212 2 10 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 74 212 (accept_3_2 19 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 74 212 2 9 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 74 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 74 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 212 2 8 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 15
  74 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 212 2 7 37 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 212 (accept_3_2 13
  74 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 212 2 6 37 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74 212
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 74 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 74 212 2 5 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 74 212 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 74 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 212 2 4 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 212 (accept_3_2 7 74 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 74 212 2 3 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 74 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 74 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 212 2 2 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 74
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 212 2 1 37 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 212 (accept_3_2 1 74
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 212 (allA_of_3_0 73 73 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 212 (allA_succ_of_accept 71 72 212
  (Polychromatic418967fa.accept_13_6_7_4_1_2264 71 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 72 212 2 35 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 72 212 (Polychromatic418967fa.accept_16_5_8_4_1_5418 69 72 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 212 4 17 18 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 212 (accept_3_2 67 72 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 212 2 33 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 212 (Polychromatic418967fa.accept_15_5_12_2_1_2820
  65 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 212 4 16 18 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 212
  (Polychromatic418967fa.accept_11_8_6_3_1_661 63 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 72 212 2 31 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 72 212 (accept_3_2 61 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 212 4 15 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 72 212 (Polychromatic418967fa.accept_15_14_12_2_1_3804 59 72 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 212 2 29 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 72 212 (Polychromatic418967fa.accept_16_9_8_4_1_1354
  57 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 212 4 14 18 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 212 (accept_3_2 55
  72 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 212 2 27 36 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 212
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 53 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 72 212 4 13 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 72 212 (Polychromatic418967fa.accept_13_12_7_4_1_3124 51 72 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 212 2 25 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 212 (accept_3_2 49 72 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 212 4 12 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 212 (Polychromatic418967fa.accept_16_15_8_4_1_1355 47 72 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 212 2 23 36 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 212
  (Polychromatic418967fa.accept_13_6_7_4_1_2264 45 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 212 4 11 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 212 (accept_3_2 43 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72
  212 2 21 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 72 212 (Polychromatic418967fa.accept_11_8_6_3_1_661 41 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 72 212 4 10 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 72 212 (Polychromatic418967fa.accept_16_7_8_4_1_689 39 72 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 212 2 19 36 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 212 (accept_3_2 37 72 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 212 4 9 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 212 (Polychromatic418967fa.accept_13_9_7_4_1_953 35
  72 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 212 2 17 36 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 212
  (Polychromatic418967fa.accept_15_3_12_2_1_507 33 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 212 4 8 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 212 (accept_3_2 31 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72
  212 2 15 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 72 212 (Polychromatic418967fa.accept_13_3_7_4_1_435 29 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 72 212 4 7 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 72 212 (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 72 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 212 2 13 36 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 212 (accept_3_2 25 72 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 212 4 6 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 212 (Polychromatic418967fa.accept_13_10_7_4_1_2262 23 72 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 212 2 11 36 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 212
  (Polychromatic418967fa.accept_15_6_12_2_1_2803 21 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 212 4 5 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 212 (accept_3_2 19 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72
  212 2 9 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  72 212 (Polychromatic418967fa.accept_16_1_8_4_1_4334 17 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 212 4 4 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 212 (Polychromatic418967fa.accept_16_15_8_4_1_1355 15 72 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 212 2 7 36 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 212 (accept_3_2 13 72 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 212 4 3 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 212 (Polychromatic418967fa.accept_13_11_7_4_1_1561 11 72 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 212 2 5 36 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 212
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 212 4 2 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 212 (accept_3_2 7 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 212
  2 3 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72
  212 (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 72 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 72 212 4 1 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 72 212 (Polychromatic418967fa.accept_13_3_7_4_1_435 3 72 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 212 2 1 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 212 (accept_3_2 1 72 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 72 212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 71 212 (allA_succ_of_accept 70 71 212 (accept_3_2 70 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 71 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 71 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 71 212 (Polychromatic418967fa.accept_19_11_14_3_1_8426 68 71
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 212 (accept_3_2 67 71 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 66
  71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 212 (accept_3_2 64 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 212 (accept_3_2 61 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 71 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 212 (accept_3_2 58 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 212 (accept_3_2 55 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 212 (Polychromatic418967fa.accept_13_2_6_4_1_1593 54 71 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 212
  (Polychromatic418967fa.accept_10_3_1_2_1_521 53 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 212 (accept_3_2 52 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 212 (accept_3_2 49 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 71 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 212 (accept_3_2 46 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 212 (Polychromatic418967fa.accept_13_5_6_4_1_1582 44 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 212 (accept_3_2 43 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 71 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 212
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 212 (accept_3_2 40 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 212 (accept_3_2 37 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 212 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 71 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 212
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 212 (accept_3_2 34 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 212 (Polychromatic418967fa.accept_26_6_19_4_1_12546 32 71 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 212 (accept_3_2 31 71 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 71 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 212 (accept_3_2 28 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 212 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 212 (accept_3_2 25 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 71 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 212
  (Polychromatic418967fa.accept_10_3_1_2_1_521 23 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 212 (accept_3_2 22 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 212 (accept_3_2 19 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 212 (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 71 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 212 (accept_3_2 16 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 212 (accept_3_2 13 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 71 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 212
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 212 (accept_3_2 10 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 212 (Polychromatic418967fa.accept_11_8_5_3_1_694 8 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 212 (accept_3_2 7 71 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 71 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 212
  (Polychromatic418967fa.accept_13_5_6_4_1_1582 5 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 212 (accept_3_2 4 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 71 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 212 (accept_3_2 1 71 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 212
  (allA_of_3_0 70 70 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 212 (allA_succ_of_accept 68 69 212
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 68 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 212 (accept_3_2 67 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 212 (accept_3_2 64 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 212 (Polychromatic418967fa.accept_16_15_5_4_1_6678 63 69 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 212 (accept_3_2 61 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 212 (accept_3_2 58 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 69 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 212 (accept_3_2 55 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 212 (accept_3_2 52 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 212 (Polychromatic418967fa.accept_10_1_9_2_1_45 51 69 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 212 (accept_3_2 49 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 212 (accept_3_2 46 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 69 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 212 (accept_3_2 43 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 212 (accept_3_2 40 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 69 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 212 (accept_3_2 37 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 212 (accept_3_2 34 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 69 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 212 (accept_3_2 31 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 212 (accept_3_2 28 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 212 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 69 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 212 (accept_3_2 25 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 212 (accept_3_2 22 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 69 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 212 (accept_3_2 19 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 212 (accept_3_2 16 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 69 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 212
  (Polychromatic418967fa.accept_21_14_6_2_1_4793 14 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 212 (accept_3_2 13 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 212 (accept_3_2 10 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 69 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 212 (accept_3_2 7 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  212 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 212 (accept_3_2 4 69 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 69 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  69 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 212 (accept_3_2 1 69 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 212 (allA_succ_of_accept 67 68
  212 (accept_3_2 67 68 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 212 2 33 34 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 212
  (Polychromatic418967fa.accept_10_5_8_2_1_517 65 68 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 212 4 16 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 68 212 (Polychromatic418967fa.accept_14_7_12_2_1_2502 63 68 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 212 2 31 34 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 212 (accept_3_2 61 68 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 212 4 15 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 68 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 212 2 29 34 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 212
  (Polychromatic418967fa.accept_25_7_18_12_1_12545 57 68 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 68 212 4 14 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 68 212 (accept_3_2 55 68 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 68 212 2 27 34 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 68 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 68 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 68 212 4 13 17 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 68 212
  (Polychromatic418967fa.accept_13_12_3_4_1_928 51 68 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 68 212 2 25 34 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 68 212 (accept_3_2 49 68 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 68 212 4 12 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 68 212 (Polychromatic418967fa.accept_19_9_11_3_1_5580 47 68 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 68 212 2 23 34 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 68 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 45
  68 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 212 4 11 17 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 212 (accept_3_2 43
  68 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 212 2 21 34 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 212
  (Polychromatic418967fa.accept_21_20_5_2_1_12544 41 68 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 68 212 4 10 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 68 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 68 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 212 2 19 34 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 212 (accept_3_2 37 68 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 212 4 9 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 68 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 68 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 212 2 17 34 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 212
  (Polychromatic418967fa.accept_13_7_3_4_1_459 33 68 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 212 4 8 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 68 212 (accept_3_2 31 68 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68
  212 2 15 34 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 68 212 (Polychromatic418967fa.accept_19_10_11_3_1_12543 29 68 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 68 212 4 7 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 68 212 (Polychromatic418967fa.accept_13_1_3_4_1_925 27 68 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 212 2 13 34 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 212 (accept_3_2 25 68 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 212 4 6 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 212 (Polychromatic418967fa.accept_11_1_2_3_1_688 23 68 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 212 2 11 34 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 212
  (Polychromatic418967fa.accept_14_7_12_2_1_2502 21 68 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 212 4 5 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 212 (accept_3_2 19 68 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  212 2 9 34 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  68 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 68 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 68 212 4 4 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 68 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 68 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 212 2 7 34 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 212 (accept_3_2 13 68 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 212 4 3 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 68 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 68 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 212 2 5 34 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 212
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 68 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 212 4 2 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 212 (accept_3_2 7 68 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 212
  2 3 34 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  212 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 68 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 68 212 4 1 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 68 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 68 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 212 2 1 34 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 212 (accept_3_2 1 68 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 212
  (allA_of_3_0 67 67 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 212 (allA_succ_of_accept 65 66 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 66 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 212 2 32 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 66 212 (Polychromatic418967fa.accept_12_3_6_8_1_969 63 66 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 212 2 31 33 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 212 (accept_3_2 61 66 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 212 2 30 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 212 (Polychromatic418967fa.accept_21_17_3_2_1_2111
  59 66 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 212 2 29 33 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 66 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 212 2 28 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 66 212 (accept_3_2 55 66 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 212 2 27 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 66 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 66 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 212 2 26 33 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 66 212
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 66 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 66 212 2 25 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 66 212 (accept_3_2 49 66 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 212 2 24 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 66 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 66 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 212 2 23 33 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 66 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 212 2 22 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 66 212 (accept_3_2 43 66 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 212 2 21 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 66 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 66 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 212 2 20 33 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 66 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 212 2 19 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 66 212 (accept_3_2 37 66 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 212 2 18 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 66 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 66 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 212 2 17 33 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 66 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 66 212 2 16 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 66 212 (accept_3_2 31 66 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 212 2 15 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 66 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 66 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 212 2 14 33 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 212
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 66 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 212 2 13 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 66 212 (accept_3_2 25 66 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 212 2 12 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 66 212 (Polychromatic418967fa.accept_13_10_1_4_1_3103 23 66 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 212 2 11 33 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 212
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 66 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 212 2 10 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 66 212 (accept_3_2 19 66 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 212 2 9 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 66 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 212 2 8 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  66 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 212 2 7 33 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 212 (accept_3_2 13
  66 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 212 2 6 33 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 66 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 212 2 5 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 66 212 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 66 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 212 2 4 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 212 (accept_3_2 7 66 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 66 212 2 3 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 66 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 66 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 212 2 2 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 212 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  66 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 212 2 1 33 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 212 (accept_3_2 1 66
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 212 (allA_succ_of_accept 64 65 212
  (accept_3_2 64 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 212
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 65 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 212 (accept_3_2 61 65 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 65 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 212 (Polychromatic418967fa.accept_15_14_5_2_1_4761
  59 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 212 (accept_3_2 58
  65 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 212
  (Polychromatic418967fa.accept_6_3_5_2_1_12 57 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 65 212 (Polychromatic418967fa.accept_15_11_5_2_1_520 56 65 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 212 (accept_3_2 55 65 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 65 212 (Polychromatic418967fa.accept_22_10_21_14_1_9394 54 65 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 212
  (Polychromatic418967fa.accept_8_5_1_4_1_628 53 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 212 (accept_3_2 52 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 65 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 212 (accept_3_2 49 65 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 65 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 212
  (Polychromatic418967fa.accept_10_7_5_2_1_880 47 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 212 (accept_3_2 46 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 65 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 212 (accept_3_2 43 65 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 65 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 212
  (Polychromatic418967fa.accept_15_11_5_2_1_520 41 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 212 (accept_3_2 40 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 212 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 65 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 212 (accept_3_2 37 65 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 212 (Polychromatic418967fa.accept_19_17_8_3_1_11211 36 65 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 212
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 212 (accept_3_2 34 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 212 (Polychromatic418967fa.accept_14_4_9_2_1_95 32 65 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 212 (accept_3_2 31 65 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 65 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 212
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 212 (accept_3_2 28 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 65 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 212 (accept_3_2 25 65 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 65 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 212
  (Polychromatic418967fa.accept_10_3_5_2_1_38 23 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 212 (accept_3_2 22 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 212 (Polychromatic418967fa.accept_18_2_11_14_1_69 20 65 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 212 (accept_3_2 19 65 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 212 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 65 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 212
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 212 (accept_3_2 16 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 65 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 212 (accept_3_2 13 65 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 65 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 212
  (Polychromatic418967fa.accept_14_11_9_2_1_6382 11 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 212 (accept_3_2 10 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 65 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 212 (accept_3_2 7 65 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 65 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 212
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 212 (accept_3_2 4 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 65 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 65 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 212 (accept_3_2 1 65 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 212
  (allA_of_3_0 64 64 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 212 (allA_succ_of_accept 62 63 212
  (Polychromatic418967fa.accept_13_10_11_4_1_2248 62 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 212 (accept_3_2 61 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 212 (Polychromatic418967fa.accept_11_5_8_3_1_66 60 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 212 (accept_3_2 58 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 212 (Polychromatic418967fa.accept_15_12_3_2_1_2756 57 63 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 212
  (Polychromatic418967fa.accept_16_8_15_4_1_5402 56 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 212 (accept_3_2 55 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 212 (accept_3_2 52 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 63 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 212
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 50 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 212 (accept_3_2 49 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 212 (Polychromatic418967fa.accept_27_21_9_23_1_12542 48 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 212 (accept_3_2 46 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 212 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 63 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 212
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 44 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 212 (accept_3_2 43 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 212 (accept_3_2 40 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 212 (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 63 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 212
  (Polychromatic418967fa.accept_11_5_8_3_1_66 38 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 212 (accept_3_2 37 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 212 (Polychromatic418967fa.accept_13_10_11_4_1_2248 36 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 212 (accept_3_2 34 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 212 (Polychromatic418967fa.accept_13_7_11_4_1_2247 33 63 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 212
  (Polychromatic418967fa.accept_13_6_11_4_1_938 32 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 212 (accept_3_2 31 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 212 (accept_3_2 28 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 63 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 212
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 26 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 212 (accept_3_2 25 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 212 (Polychromatic418967fa.accept_16_8_15_4_1_5402 24 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 212 (accept_3_2 22 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 212 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 63 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 212
  (Polychromatic418967fa.accept_13_7_11_4_1_2247 20 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 212 (accept_3_2 19 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 212 (accept_3_2 16 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 212 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 63 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 212
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 212 (accept_3_2 13 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 212 (Polychromatic418967fa.accept_13_12_11_4_1_3111 12 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 212 (accept_3_2 10 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 212 (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 63 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 212
  (Polychromatic418967fa.accept_13_8_11_4_1_1553 8 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 212 (accept_3_2 7 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  212 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 63 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 212 (accept_3_2 4 63 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 63 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 212
  (Polychromatic418967fa.accept_13_2_11_4_1_445 2 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 212 (accept_3_2 1 63 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 212 (allA_succ_of_accept 61 62 212
  (accept_3_2 61 62 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 212 2 30 31 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 62 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 212 2 29 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 62 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 62 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 212 2 28 31 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 212 (accept_3_2 55 62 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 212 2 27 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 53
  62 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 212 2 26 31 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 212
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 62 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 212 2 25 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 62 212 (accept_3_2 49 62 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 62 212 2 24 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 62 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 62 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 212 2 23 31 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 62 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 212 2 22 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 62 212 (accept_3_2 43 62 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 62 212 2 21 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 62 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 62 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 62 212 2 20 31 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 62 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 62 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 62 212 2 19 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 62 212 (accept_3_2 37 62 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 62 212 2 18 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 62 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 62 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 212 2 17 31 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 212
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 62 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 212 2 16 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 62 212 (accept_3_2 31 62 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 62 212 2 15 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 62 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 62 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 212 2 14 31 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 212
  (Polychromatic418967fa.accept_13_1_10_4_1_954 27 62 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 212 2 13 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 62 212 (accept_3_2 25 62 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 62 212 2 12 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 62 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 62 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 62 212 2 11 31 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 62 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 62 212 2 10 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 62 212 (accept_3_2 19 62 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 62 212 2 9 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 62 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 62 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 212 2 8 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  62 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 212 2 7 31 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 212 (accept_3_2 13
  62 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 212 2 6 31 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 62 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 62 212 2 5 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 62 212 (Polychromatic418967fa.accept_16_9_14_4_1_3225 9 62 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 212 2 4 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 212 (accept_3_2 7 62 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 212 2 3 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 62 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 212 2 2 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 62
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 212 2 1 31 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 212 (accept_3_2 1 62
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 212 (allA_of_3_0 61 61 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 212 (allA_succ_of_accept 59 60 212
  (Polychromatic418967fa.accept_16_11_12_4_1_3195 59 60 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 212 2 29 30 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 60 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 60 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 212 4 14 15 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 212 (accept_3_2 55 60 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 212 2 27 30 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 53
  60 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 212 4 13 15 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 212
  (Polychromatic418967fa.accept_13_12_8_4_1_3099 51 60 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 212 2 25 30 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 60 212 (accept_3_2 49 60 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 212 4 12 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 60 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 212 2 23 30 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 60 212 (Polychromatic418967fa.accept_16_13_12_4_1_4323
  45 60 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 212 4 11 15 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 212 (accept_3_2 43
  60 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 212 2 21 30 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 212
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 60 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 212 4 10 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 60 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 60 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 212 2 19 30 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 212 (accept_3_2 37 60 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 212 4 9 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 60 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 60 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 212 2 17 30 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 60 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 212 4 8 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 212 (accept_3_2 31 60 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  212 2 15 30 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 60 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 60 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 212 4 7 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 60 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 212 2 13 30 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 212 (accept_3_2 25 60 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 212 4 6 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 212 (Polychromatic418967fa.accept_13_10_8_4_1_3098 23 60 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 212 2 11 30 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 60 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 212 4 5 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 212 (accept_3_2 19 60 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60
  212 2 9 30 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  60 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 60 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 212 4 4 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 60 212 (Polychromatic418967fa.accept_16_15_12_4_1_4324 15 60 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 212 2 7 30 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 212 (accept_3_2 13 60 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 212 4 3 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 11
  60 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 212 2 5 30 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 212
  (Polychromatic418967fa.accept_13_9_8_4_1_937 9 60 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 212 4 2 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 212 (accept_3_2 7 60 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 212
  2 3 30 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60
  212 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 60 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 60 212 4 1 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 60 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 60 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 212 2 1 30 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 212 (accept_3_2 1 60 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 212
  (allA_succ_of_accept 58 59 212 (accept_3_2 58 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 212 (Polychromatic418967fa.accept_16_8_11_4_1_3290 56 59 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 212 (accept_3_2 55 59 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 59 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 212
  (Polychromatic418967fa.accept_20_13_19_12_1_5143 53 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 59 212 (accept_3_2 52 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 59 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 59 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 59 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 212 (accept_3_2 49 59 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 48
  59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 212 (accept_3_2 46 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 212 (Polychromatic418967fa.accept_16_12_11_4_1_1359 44 59 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 212 (accept_3_2 43 59 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 212 (Polychromatic418967fa.accept_13_3_7_4_1_435 42 59 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 212
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 212 (accept_3_2 40 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 59 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 212 (accept_3_2 37 59 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 59 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 212
  (Polychromatic418967fa.accept_13_9_7_4_1_953 35 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 212 (accept_3_2 34 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 212 (Polychromatic418967fa.accept_13_6_7_4_1_2264 32 59 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 212 (accept_3_2 31 59 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 212 (Polychromatic418967fa.accept_19_11_2_3_1_8424 30 59 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 212 (accept_3_2 28 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 59 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 212 (accept_3_2 25 59 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 212 (Polychromatic418967fa.accept_13_11_7_4_1_1561 24 59 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 212
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 212 (accept_3_2 22 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 59 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 212 (accept_3_2 19 59 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 212 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 59 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 212
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 212 (accept_3_2 16 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 59 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 212 (accept_3_2 13 59 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 59 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 212
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 212 (accept_3_2 10 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 59 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 212 (accept_3_2 7 59 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 59 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 212 (accept_3_2 4 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 59 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 212 (accept_3_2 1 59 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 212 (allA_of_3_0
  58 58 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 212 (allA_succ_of_accept 56 57 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 212 (accept_3_2 55 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 212 (accept_3_2 52 57 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 57 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 212
  (Polychromatic418967fa.accept_14_8_1_2_1_965 50 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 212 (accept_3_2 49 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 57 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 212 (accept_3_2 46 57 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 57 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 212 (accept_3_2 43 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 212 (accept_3_2 40 57 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 212 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 57 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 212 (accept_3_2 37 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 212 (Polychromatic418967fa.accept_13_10_5_4_1_3107 36 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 57 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 212 (accept_3_2 34 57 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 57 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 212
  (Polychromatic418967fa.accept_13_6_5_4_1_3924 32 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 212 (accept_3_2 31 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 212 (accept_3_2 28 57 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 57 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 212 (accept_3_2 25 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 57 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 212 (accept_3_2 22 57 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 212 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 57 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 212
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 212 (accept_3_2 19 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 212 (accept_3_2 16 57 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 57 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 212
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 212 (accept_3_2 13 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 212 (Polychromatic418967fa.accept_11_1_2_3_1_688 12 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 57 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 212 (accept_3_2 10 57 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 212 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 57 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 212 (accept_3_2 7 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  212 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 57 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 212 (accept_3_2 4 57 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 57 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 57
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 212 (accept_3_2 1 57 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 212 (allA_succ_of_accept 55 56 212 (accept_3_2 55 56 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 212 2 27 28 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 56 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 56 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 212 4 13 14 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 212
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 56 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 56 212 2 25 28 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 56 212 (accept_3_2 49 56 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 56 212 4 12 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 56 212 (Polychromatic418967fa.accept_16_15_8_4_1_1355 47 56 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 56 212 2 23 28 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 56 212 (Polychromatic418967fa.accept_16_13_8_4_1_3250
  45 56 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 212 4 11 14 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 212 (accept_3_2 43
  56 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 212 2 21 28 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 212
  (Polychromatic418967fa.accept_10_1_6_2_1_867 41 56 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 56 212 4 10 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 56 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 56 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 56 212 2 19 28 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 56 212 (accept_3_2 37 56 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56 212 4 9 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 56 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 56 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 212 2 17 28 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 212
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 56 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 212 4 8 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 56 212 (accept_3_2 31 56 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56
  212 2 15 28 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 56 212 (Polychromatic418967fa.accept_16_13_8_4_1_3250 29 56 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 56 212 4 7 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 56 212 (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 56 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 212 2 13 28 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 212 (accept_3_2 25 56 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 212 4 6 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 212 (Polychromatic418967fa.accept_16_7_8_4_1_689 23 56 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 212 2 11 28 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 56 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 212 4 5 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 212 (accept_3_2 19 56 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  212 2 9 28 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 212 4 4 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 56 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 212 2 7 28 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 212 (accept_3_2 13 56 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 212 4 3 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56 212 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 56 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 212 2 5 28 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 212
  (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 56 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 212 4 2 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 56 212 (accept_3_2 7 56 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 212
  2 3 28 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56
  212 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 56 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 56 212 4 1 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 56 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 56 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 212 2 1 28 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 212 (accept_3_2 1 56 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 56 212)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 212
  (allA_of_3_0 55 55 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 212 (allA_succ_of_accept 53 54 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 54 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 212 2 26 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 54 212 (Polychromatic418967fa.accept_11_7_10_3_1_633 51 54 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 212 2 25 27 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 212 (accept_3_2 49 54 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 212 2 24 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 212 (Polychromatic418967fa.accept_10_7_4_2_1_903 47
  54 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 212 2 23 27 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 54 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 212 2 22 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 54 212 (accept_3_2 43 54 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 212 2 21 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 54 212 (Polychromatic418967fa.accept_15_11_9_2_1_4780 41 54 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 212 2 20 27 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 54 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 54 212 2 19 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 54 212 (accept_3_2 37 54 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 212 2 18 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 54 212 (Polychromatic418967fa.accept_14_7_12_2_1_2502 35 54 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 212 2 17 27 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 54 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 54 212 2 16 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 54 212 (accept_3_2 31 54 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 212 2 15 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 54 212 (Polychromatic418967fa.accept_11_7_10_3_1_633 29 54 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 212 2 14 27 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 212
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 54 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 212 2 13 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 54 212 (accept_3_2 25 54 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 212 2 12 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 212 (Polychromatic418967fa.accept_15_8_9_2_1_1897 23 54 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 212 2 11 27 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 54 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 54 212 2 10 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 54 212 (accept_3_2 19 54 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 212 2 9 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 54 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 212 2 8 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 212 (Polychromatic418967fa.accept_12_3_6_8_1_969 15
  54 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 212 2 7 27 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 212 (accept_3_2 13
  54 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 212 2 6 27 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 54 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 54 212 2 5 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 54 212 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 54 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 212 2 4 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 212 (accept_3_2 7 54 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 54 212 2 3 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 54 212 (Polychromatic418967fa.accept_13_5_2_4_1_3955 5 54 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 212 2 2 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 54
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 212 2 1 27 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 212 (accept_3_2 1 54
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 212))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 212 (allA_succ_of_accept 52 53 212 (accept_3_2 52 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 53 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 53 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 53 212 (Polychromatic418967fa.accept_11_6_9_3_1_1103 50 53 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 212 (accept_3_2 49 53 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 48
  53 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 212 (accept_3_2 46 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 212 (Polychromatic418967fa.accept_13_5_1_4_1_3966 44 53 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 212 (accept_3_2 43 53 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 53 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 212
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 212 (accept_3_2 40 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 53 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 212 (accept_3_2 37 53 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 212 (Polychromatic418967fa.accept_13_10_1_4_1_3103 36 53 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 212
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 212 (accept_3_2 34 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 212 (Polychromatic418967fa.accept_23_9_7_5_1_12541 32 53 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 212 (accept_3_2 31 53 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 53 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 212 (accept_3_2 28 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 53 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 212 (accept_3_2 25 53 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 53 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 212
  (Polychromatic418967fa.accept_13_10_1_4_1_3103 23 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 212 (accept_3_2 22 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 53 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 212 (accept_3_2 19 53 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 212 (Polychromatic418967fa.accept_13_5_1_4_1_3966 18 53 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 212
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 212 (accept_3_2 16 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 53 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 212 (accept_3_2 13 53 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 53 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 212 (accept_3_2 10 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 212 (Polychromatic418967fa.accept_16_8_5_4_1_674 8 53 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 212 (accept_3_2 7 53 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 53 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 212 (accept_3_2 4 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 53 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 53 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 212 (accept_3_2 1 53 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 212))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 212 (allA_of_3_0 52 52
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 212 (allA_succ_of_accept 50 51 212
  (Polychromatic418967fa.accept_13_11_12_4_1_3945 50 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 212 (accept_3_2 49 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 51 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 212 (accept_3_2 46 51 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 212 (Polychromatic418967fa.accept_19_7_13_3_1_4171 45 51 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 212 (accept_3_2 43 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 51 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 212 (accept_3_2 40 51 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 51 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 212 (accept_3_2 37 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 212 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 212 (accept_3_2 34 51 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 212 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 51 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 212
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 32 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 212 (accept_3_2 31 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 51 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 212 (accept_3_2 28 51 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 212 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 51 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 212 (accept_3_2 25 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 212 (Polychromatic418967fa.accept_13_11_12_4_1_3945 24 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 212 (accept_3_2 22 51 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 51 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 212 (accept_3_2 19 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 51 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 212 (accept_3_2 16 51 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 51 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 212
  (Polychromatic418967fa.accept_21_14_9_2_1_8005 14 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 212 (accept_3_2 13 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 212 (accept_3_2 10 51 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 212 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 51 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 212 (accept_3_2 7 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  212 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 51 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 51 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 212 (accept_3_2 4 51 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 51 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  51 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 212 (accept_3_2 1 51 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 212)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 212 (allA_succ_of_accept 49 50 212 (accept_3_2 49 50 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 50 212 2 24 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 50 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 50 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 50 212 2 23 25 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 50 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 50 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 50 212 2 22 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 50 212 (accept_3_2 43 50 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 50 212 2 21 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 50 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 50 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 212 2 20 25 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 212
  (Polychromatic418967fa.accept_31_8_19_26_1_12540 39 50 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 50 212 2 19 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 50 212 (accept_3_2 37 50 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 50 212 2 18 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 50 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 50 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 212 2 17 25 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 212
  (Polychromatic418967fa.accept_13_7_11_4_1_2247 33 50 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 212 2 16 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 50 212 (accept_3_2 31 50 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 50 212 2 15 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 50 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 50 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 50 212 2 14 25 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 50 212
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 50 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 50 212 2 13 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 50 212 (accept_3_2 25 50 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 50 212 2 12 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 50 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 50 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 212 2 11 25 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 212
  (Polychromatic418967fa.accept_13_8_11_4_1_1553 21 50 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 212 2 10 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 50 212 (accept_3_2 19 50 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 50 212 2 9 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 50 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 50 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 212 2 8 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 212 (Polychromatic418967fa.accept_13_2_11_4_1_445
  15 50 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 212 2 7 25 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 212 (accept_3_2 13
  50 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 212 2 6 25 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 212
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 50 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 212 2 5 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 212 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 50 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 212 2 4 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 212 (accept_3_2 7 50 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 50 212 2 3 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 50 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 50 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 212 2 2 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 50
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 212 2 1 25 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 212 (accept_3_2 1 50
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 212))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 49 212 (allA_of_3_0 49 49 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 212
  (allA_succ_of_accept 47 48 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 48 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 212 2 23 24 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 45
  48 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 212 4 11 12 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 212 (accept_3_2 43
  48 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 212 2 21 24 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 212
  (Polychromatic418967fa.accept_17_7_14_8_1_5069 41 48 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 48 212 4 10 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 48 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 48 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 212 2 19 24 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 212 (accept_3_2 37 48 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 212 4 9 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 48 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 48 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 212 2 17 24 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 212
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 48 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 48 212 4 8 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 212 (accept_3_2 31 48 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48
  212 2 15 24 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 48 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 48 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 48 212 4 7 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 48 212 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 48 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 212 2 13 24 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 212 (accept_3_2 25 48 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 212 4 6 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 212 (Polychromatic418967fa.accept_17_6_14_8_1_3858 23 48 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 212 2 11 24 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 212
  (Polychromatic418967fa.accept_13_8_9_4_1_1552 21 48 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 212 4 5 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 212 (accept_3_2 19 48 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48
  212 2 9 24 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  48 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 48 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 212 4 4 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 48 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 212 2 7 24 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 212 (accept_3_2 13 48 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 212 4 3 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 48 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 212 2 5 24 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 212
  (Polychromatic418967fa.accept_19_9_10_3_1_1738 9 48 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 212 4 2 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 212 (accept_3_2 7 48 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 212
  2 3 24 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48
  212 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 48 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 48 212 4 1 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 48 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 48 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 212 2 1 24 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 212 (accept_3_2 1 48 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 212)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 212 (allA_succ_of_accept 46
  47 212 (accept_3_2 46 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 212
  (Polychromatic418967fa.accept_6_3_5_2_1_12 45 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 47 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 212 (accept_3_2 43 47 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 47 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 212
  (Polychromatic418967fa.accept_18_5_11_14_1_7203 41 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 212 (accept_3_2 40 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 47 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 212 (accept_3_2 37 47 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 212 (Polychromatic418967fa.accept_13_10_8_4_1_3098 36 47 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 212
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 212 (accept_3_2 34 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 47 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 212 (accept_3_2 31 47 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 47 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 212
  (Polychromatic418967fa.accept_10_9_7_2_1_887 29 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 212 (accept_3_2 28 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 47 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 212 (accept_3_2 25 47 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 47 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 212
  (Polychromatic418967fa.accept_13_10_8_4_1_3098 23 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 212 (accept_3_2 22 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 212 (Polychromatic418967fa.accept_17_3_13_8_1_11337 20 47 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 212 (accept_3_2 19 47 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 47 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 212 (accept_3_2 16 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 47 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 212 (accept_3_2 13 47 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 47 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 212 (accept_3_2 10 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 47 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 212 (accept_3_2 7 47 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 47 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 212
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 212 (accept_3_2 4 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 47 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 212 (accept_3_2 1 47 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 212))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 212 (allA_of_3_0 46 46 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 212 (allA_succ_of_accept 44 45 212
  (Polychromatic418967fa.accept_13_5_6_4_1_1582 44 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 212 (accept_3_2 43 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 212 (accept_3_2 40 45 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 212 (Polychromatic418967fa.accept_16_7_13_4_1_1348 39 45 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 212
  (Polychromatic418967fa.accept_10_8_5_2_1_881 38 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 212 (accept_3_2 37 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 45 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 212 (accept_3_2 34 45 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 45 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 212
  (Polychromatic418967fa.accept_19_13_7_3_1_9798 32 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 212 (accept_3_2 31 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 212 (accept_3_2 28 45 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 45 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 212 (accept_3_2 25 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 212 (Polychromatic418967fa.accept_11_2_1_3_1_683 24 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 45 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 212 (accept_3_2 22 45 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 212 (Polychromatic418967fa.accept_18_3_9_14_1_2219 21 45 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 212
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 212 (accept_3_2 19 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 212 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 212 (accept_3_2 16 45 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 45 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 212
  (Polychromatic418967fa.accept_17_14_11_8_1_3854 14 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 212 (accept_3_2 13 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 45 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 212 (accept_3_2 10 45 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 45 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 212 (accept_3_2 7 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  212 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 45 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 212 (accept_3_2 4 45 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 212 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 45 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 212 (Polychromatic418967fa.accept_11_2_1_3_1_683 2
  45 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 212 (accept_3_2 1 45 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 212))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  212 (allA_succ_of_accept 43 44 212 (accept_3_2 43 44 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  44 212 2 21 22 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 44 212 (Polychromatic418967fa.accept_13_2_5_4_1_3926 41 44 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 44 212 4 10 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 44 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 39
  44 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 212 2 19 22 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 212 (accept_3_2 37
  44 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 212 4 9 11 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 212
  (Polychromatic418967fa.accept_13_9_5_4_1_1591 35 44 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 44 212 2 17 22 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 44 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 44 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 44 212 4 8 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 212 (accept_3_2 31 44 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 212 2 15 22 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 44 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 44 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 212 4 7 11 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 212
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 44 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 212 2 13 22 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 44 212 (accept_3_2 25 44 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 44 212 4 6 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 44 212 (Polychromatic418967fa.accept_13_10_5_4_1_3107 23 44 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 212 2 11 22 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 21
  44 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 212 4 5 11 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 212 (accept_3_2 19
  44 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 212 2 9 22 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 44 212
  (Polychromatic418967fa.accept_10_7_4_2_1_903 17 44 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 44 212 4 4 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 44 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 44 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 212 2 7 22 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 212 (accept_3_2 13 44 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 212 4 3 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 44 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 44 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 212 2 5 22 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 212
  (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 44 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 44 212 4 2 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 44 212 (accept_3_2 7 44 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 212
  2 3 22 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44
  212 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 44 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 44 212 4 1 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 44 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 44 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 212 2 1 22 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 212 (accept_3_2 1 44 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 44 212)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 212 (allA_of_3_0 43 43
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 212 (allA_succ_of_accept 41 42 212
  (Polychromatic418967fa.accept_27_14_15_23_1_12539 41 42 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 42 212 2 20 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 42 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 42 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 212 2 19 21 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 212 (accept_3_2 37 42 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 212 2 18 21 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 42 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 42 212 2 17 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 42 212 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 42 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 212 2 16 21 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 212 (accept_3_2 31 42 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 212 2 15 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 29
  42 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 212 2 14 21 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 42 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 42 212 2 13 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 42 212 (accept_3_2 25 42 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 212 2 12 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 42 212 (Polychromatic418967fa.accept_22_1_20_14_1_11000 23 42 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 212 2 11 21 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 42 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 212 2 10 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 42 212 (accept_3_2 19 42 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 212 2 9 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 42 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 212 2 8 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 212 (Polychromatic418967fa.accept_12_3_6_8_1_969 15
  42 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 212 2 7 21 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 212 (accept_3_2 13
  42 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 212 2 6 21 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 42 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 42 212 2 5 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 42 212 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 42 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 212 2 4 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 212 (accept_3_2 7 42 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 42 212 2 3 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 42 212 (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 42 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 212 2 2 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 42
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 212 2 1 21 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 212 (accept_3_2 1 42
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 212)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41
  212 (allA_succ_of_accept 40 41 212 (accept_3_2 40 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 41 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 41 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 212 (accept_3_2 37 41 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 41 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 212
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 212 (accept_3_2 34 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 41 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 212 (accept_3_2 31 41 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 212 (Polychromatic418967fa.accept_16_14_9_4_1_6693 30 41 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 212 (accept_3_2 28 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 212 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 41 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 212 (accept_3_2 25 41 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 41 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 212
  (Polychromatic418967fa.accept_10_3_1_2_1_521 23 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 212 (accept_3_2 22 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 212 (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 41 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 212 (accept_3_2 19 41 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 41 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 212 (accept_3_2 16 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 41 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 212 (accept_3_2 13 41 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 212 (Polychromatic418967fa.accept_13_12_2_4_1_3131 12 41 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 212 (accept_3_2 10 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 41 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 212 (accept_3_2 7 41 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 212 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 41 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 212
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 212 (accept_3_2 4 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 41 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 41 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 212 (accept_3_2 1 41 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 212))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 212 (allA_of_3_0 40 40 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 212 (allA_succ_of_accept 38 39 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 212 (accept_3_2 37 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 212 (Polychromatic418967fa.accept_19_17_1_3_1_4160 36 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 212 (accept_3_2 34 39 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 39 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 212
  (Polychromatic418967fa.accept_23_9_16_5_1_7482 32 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 212 (accept_3_2 31 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 212 (Polychromatic418967fa.accept_11_8_6_3_1_661 30 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 39 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 212 (accept_3_2 28 39 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 39 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 212 (accept_3_2 25 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 212 (accept_3_2 22 39 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 212 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 39 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 212
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 212 (accept_3_2 19 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 39 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 212 (accept_3_2 16 39 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 39 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 212
  (Polychromatic418967fa.accept_16_14_7_4_1_3243 14 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 212 (accept_3_2 13 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 212 (accept_3_2 10 39 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 212 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 39 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 212 (accept_3_2 7 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  212 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 39 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 39 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 212 (accept_3_2 4 39 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 39 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 39
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 212 (accept_3_2 1 39 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 212))))))))))))))))))))))))))))))))))))))) (allB_succ 38 212
  (allA_succ_of_accept 37 38 212 (accept_3_2 37 38 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  212 2 18 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  35 38 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 38 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 212 2 17 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 38 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 212 2 16 19 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 212 (accept_3_2 31 38 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 212 2 15 19 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 38 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 212 2 14 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 38 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 38 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 212 2 13 19 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 212 (accept_3_2 25 38 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 212 2 12 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 212 (Polychromatic418967fa.accept_12_11_2_8_1_511
  23 38 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 212 2 11 19 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 38 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 212 2 10 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 38 212 (accept_3_2 19 38 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 38 212 2 9 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 38 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 38 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 212 2 8 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  38 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 212 2 7 19 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 212 (accept_3_2 13
  38 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 212 2 6 19 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 38 212
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 38 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 38 212 2 5 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 38 212 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 38 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 212 2 4 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 212 (accept_3_2 7 38 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 38 212 2 3 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 38 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 38 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 212 2 2 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 38
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 212 2 1 19 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 212 (accept_3_2 1 38
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 212)))))))))))))))))))))))))))))))))))))) (allB_succ 37 212
  (allA_of_3_0 37 37 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 212 (allA_succ_of_accept 35 36 212
  (Polychromatic418967fa.accept_19_16_17_3_1_2916 35 36 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 212 2 17 18 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 36 212 (Polychromatic418967fa.accept_13_7_10_4_1_919 33 36 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 212 4 8 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 212 (accept_3_2 31 36 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 212 2 15 18 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 212 (Polychromatic418967fa.accept_14_1_8_2_1_1675 29 36 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 212 4 7 9 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 212
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 36 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 212 2 13 18 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 36 212 (accept_3_2 25 36 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 212 4 6 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 212 (Polychromatic418967fa.accept_15_8_6_2_1_1128 23 36 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 212 2 11 18 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 212 (Polychromatic418967fa.accept_10_1_6_2_1_867 21
  36 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 212 4 5 9 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 212 (accept_3_2 19
  36 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 212 2 9 18 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 36 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 36 212 4 4 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 36 212 (Polychromatic418967fa.accept_14_1_8_2_1_1675 15 36 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 212 2 7 18 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 212 (accept_3_2 13 36 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 212 4 3 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 36 212 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 36 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 212 2 5 18 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 36 212
  (Polychromatic418967fa.accept_21_9_15_2_1_4765 9 36 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 36 212 4 2 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 212 (accept_3_2 7 36 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 212
  2 3 18 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36
  212 (Polychromatic418967fa.accept_13_5_10_4_1_1564 5 36 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 36 212 4 1 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 36 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 36 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 212 2 1 18 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 212 (accept_3_2 1 36 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 36 212)))))))))))))))))))))))))))))))))))) (allB_succ 35 212 (allA_succ_of_accept 34 35
  212 (accept_3_2 34 35 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 212
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 35 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 212 (Polychromatic418967fa.accept_13_6_9_4_1_2288 32 35 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 212 (accept_3_2 31 35 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 35 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 29
  35 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 212 (accept_3_2 28 35
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 212 (Polychromatic418967fa.accept_6_3_5_2_1_12
  27 35 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 212
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 35 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 212 (accept_3_2 25 35 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 35 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 212 (accept_3_2 22 35 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 35 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 35 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 212 (accept_3_2 19 35 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 212 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 35 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 212 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 35 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 212 (accept_3_2 16 35 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 212
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 35 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 212 (accept_3_2 13 35 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 35 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 35 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 212 (accept_3_2 10 35 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 35 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 212
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 35 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 212 (accept_3_2 7 35 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  212 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 35 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 212 (Polychromatic418967fa.accept_13_5_9_4_1_441 5 35 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 212 (accept_3_2 4 35 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  35 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 212 (accept_3_2 1 35 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 212))))))))))))))))))))))))))))))))))) (allB_succ 34 212
  (allA_of_3_0 34 34 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 212 (allA_succ_of_accept 32 33 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 33 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 212 (accept_3_2 31 33 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 33 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 212 (accept_3_2 28 33 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 212 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 33 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 33 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 212 (accept_3_2 25 33 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 33 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 33 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 212 (accept_3_2 22 33 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 212 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 33 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 33 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 212 (accept_3_2 19 33 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 33 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 212 (accept_3_2 16 33 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 212 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 33 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 212
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 33 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 212 (accept_3_2 13 33 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 33 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 33 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 212 (accept_3_2 10 33 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 212 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 33 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 33 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 212 (accept_3_2 7 33 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  212 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 33 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 212 (accept_3_2 4 33 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 33 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  33 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 212 (accept_3_2 1 33 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 212))))))))))))))))))))))))))))))))) (allB_succ 32 212
  (allA_succ_of_accept 31 32 212 (accept_3_2 31 32 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32
  212 2 15 16 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 32 212 (Polychromatic418967fa.accept_11_7_10_3_1_633 29 32 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 32 212 4 7 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 32 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 32 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 212 2 13 16 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 212 (accept_3_2 25 32 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 212 4 6 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 212 (Polychromatic418967fa.accept_13_10_6_4_1_1583 23 32 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 212 2 11 16 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 212
  (Polychromatic418967fa.accept_22_21_10_14_1_11003 21 32 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 32 212 4 5 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 32 212 (accept_3_2 19 32 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 32 212 2 9 16 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 32 212 (Polychromatic418967fa.accept_21_17_11_2_1_7953 17 32 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 32 212 4 4 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 32 212 (Polychromatic418967fa.accept_13_2_6_4_1_1593 15 32 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 212 2 7 16 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 212 (accept_3_2 13
  32 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 212 4 3 8 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 32 212
  (Polychromatic418967fa.accept_13_11_6_4_1_3121 11 32 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 32 212 2 5 16 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 32 212 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 32 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 212 4 2 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 212 (accept_3_2 7 32 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 32 212 2 3 16 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 32 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 32 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 32 212 4 1 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 32 212 (Polychromatic418967fa.accept_24_3_8_20_1_12538
  3 32 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 212 2 1 16 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 212 (accept_3_2 1 32
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 212)))))))))))))))))))))))))))))))) (allB_succ 31 212
  (allA_of_3_0 31 31 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 212 (allA_succ_of_accept 29 30 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 30 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 212 2 14 15 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 30 212 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 30 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 212 2 13 15 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 212 (accept_3_2 25 30 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 212 2 12 15 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 212 (Polychromatic418967fa.accept_16_7_14_4_1_1362
  23 30 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 212 2 11 15 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 30 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 212 2 10 15 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 30 212 (accept_3_2 19 30 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 212 2 9 15 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 30 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 212 2 8 15 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  30 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 212 2 7 15 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 212 (accept_3_2 13
  30 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 212 2 6 15 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 30 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 212 2 5 15 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 30 212 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 30 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 212 2 4 15 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 212 (accept_3_2 7 30 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 30 212 2 3 15 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 30 212 (Polychromatic418967fa.accept_11_5_8_3_1_66 5 30 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 212 2 2 15 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 212 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  30 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 212 2 1 15 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 212 (accept_3_2 1 30
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 212)))))))))))))))))))))))))))))) (allB_succ 29 212
  (allA_succ_of_accept 28 29 212 (accept_3_2 28 29 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  29 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 29 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 29 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 29 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 212 (accept_3_2 25 29 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 29 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 212
  (Polychromatic418967fa.accept_16_7_13_4_1_1348 23 29 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 212 (accept_3_2 22 29 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 29 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 29 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 212 (accept_3_2 19 29 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 212 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 29 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 29 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 212 (accept_3_2 16 29 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 29 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 29 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 212 (accept_3_2 13 29 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 29 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 212
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 29 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 212 (accept_3_2 10 29 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 212 (accept_3_2 7 29 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 29 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 212
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 29 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 212 (accept_3_2 4 29 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 29 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 29 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 212 (accept_3_2 1 29 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 212))))))))))))))))))))))))))))) (allB_succ 28 212 (allA_of_3_0 28 28 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 212 (allA_succ_of_accept 26 27 212 (Polychromatic418967fa.accept_20_6_7_12_1_8197
  26 27 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 212 (accept_3_2 25
  27 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 27 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 212 (accept_3_2 22 27 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 212 (Polychromatic418967fa.accept_15_6_12_2_1_2803 21 27 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 212
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 27 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 212 (accept_3_2 19 27 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 27 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 27 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 212 (accept_3_2 16 27 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 27 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 212
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 27 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 212 (accept_3_2 13 27 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 212 (Polychromatic418967fa.accept_16_12_11_4_1_1359 12 27 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 212 (accept_3_2 10 27 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 212 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 27 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 27 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 212 (accept_3_2 7 27 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  212 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 27 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 27 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 212 (accept_3_2 4 27 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 27 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 212 (Polychromatic418967fa.accept_17_2_10_8_1_7691
  2 27 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 212 (accept_3_2 1 27
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 212))))))))))))))))))))))))))) (allB_succ 26 212
  (allA_succ_of_accept 25 26 212 (accept_3_2 25 26 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  212 2 12 13 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  23 26 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 26 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 212 2 11 13 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 26 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 212 2 10 13 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 212 (accept_3_2 19 26 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 212 2 9 13 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 26 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 26 212 2 8 13 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 26 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 26 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 26 212 2 7 13 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 26 212 (accept_3_2 13 26 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 212 2 6 13 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 26 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 26 212 2 5 13 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 26 212
  (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 26 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 26 212 2 4 13 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 26 212 (accept_3_2 7 26 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 212
  2 3 13 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26
  212 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 26 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 26 212 2 2 13 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 26 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 26 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 212 2 1 13 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 212 (accept_3_2 1 26 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 212)))))))))))))))))))))))))) (allB_succ 25 212 (allA_of_3_0 25 25 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 24 212 (allA_succ_of_accept 23 24 212 (Polychromatic418967fa.accept_11_1_2_3_1_688 23
  24 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 212 2 11 12 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 24 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 212 4 5 6 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 212 (accept_3_2 19 24 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  212 2 9 12 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 212 4 4 6 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 24 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 212 2 7 12 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 212 (accept_3_2 13 24 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 212 4 3 6 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 24 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 212 2 5 12 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 212
  (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 24 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 212 4 2 6 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 212 (accept_3_2 7 24 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 212
  2 3 12 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  212 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 24 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 212 4 1 6 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 24 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 212 2 1 12 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 212 (accept_3_2 1 24 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 212)))))))))))))))))))))))) (allB_succ 23 212 (allA_succ_of_accept 22 23 212 (accept_3_2 22
  23 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 212
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 23 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 212 (Polychromatic418967fa.accept_13_7_10_4_1_919 20 23 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 212 (accept_3_2 19 23 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 212 (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 23 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 212
  (Polychromatic418967fa.accept_25_17_23_12_1_12537 17 23 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 23 212 (accept_3_2 16 23 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 23 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 23 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 23 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 212 (accept_3_2 13 23 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 212 (Polychromatic418967fa.accept_16_12_7_4_1_687
  12 23 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 212
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 23 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 212 (accept_3_2 10 23 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 23 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 212 (Polychromatic418967fa.accept_13_8_10_4_1_2270 8 23 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 212 (accept_3_2 7 23 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 212 (Polychromatic418967fa.accept_13_6_10_4_1_957 6 23 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 212
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 23 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 212 (accept_3_2 4 23 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 212 (Polychromatic418967fa.accept_11_2_1_3_1_683 2 23 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 212 (accept_3_2 1 23 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 212))))))))))))))))))))))) (allB_succ 22 212 (allA_of_3_0 22 22 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 21 212 (allA_succ_of_accept 20 21 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 21
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 212 (accept_3_2 19 21 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 212 (Polychromatic418967fa.accept_11_7_10_3_1_633
  18 21 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 212 (accept_3_2 16 21 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 21 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 21 212 (Polychromatic418967fa.accept_27_14_21_23_1_4593 14 21 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 212 (accept_3_2 13 21 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 212 (Polychromatic418967fa.accept_13_12_8_4_1_3099 12 21
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 21 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 212 (accept_3_2 10 21 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 21 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 21 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 212 (accept_3_2 7 21 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 21 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 212 (accept_3_2 4 21 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  212 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 21 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 21 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 212 (accept_3_2 1 21 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 21 212))))))))))))))))))))) (allB_succ 20 212 (allA_succ_of_accept 19 20 212 (accept_3_2 19 20
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 212 2 9 10 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 20 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 212 4 4 5 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 20 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 212 2 7 10 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 212 (accept_3_2 13 20 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 212 4 3 5 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 20 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 20 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 212 2 5 10 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 212
  (Polychromatic418967fa.accept_13_9_7_4_1_953 9 20 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 212 4 2 5 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 212 (accept_3_2 7 20 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 212
  2 3 10 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  212 (Polychromatic418967fa.accept_17_5_3_8_1_1697 5 20 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 20 212 4 1 5 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 20 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 20 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 212 2 1 10 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 212 (accept_3_2 1 20 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 20 212)))))))))))))))))))) (allB_succ 19 212 (allA_of_3_0 19 19 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 18 212 (allA_succ_of_accept 17 18 212 (Polychromatic418967fa.accept_23_17_18_5_1_7391
  17 18 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 212 2 8 9 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 212
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 18 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 212 2 7 9 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 212 (accept_3_2 13 18 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  212 2 6 9 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 212 (Polychromatic418967fa.accept_17_11_1_8_1_7502 11 18 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 212 2 5 9 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 212 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 18 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 212 2 4 9 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 212 (accept_3_2 7 18 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 212 2 3 9 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 18 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 212 2 2 9 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 18 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 212 2 1 9 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 212 (accept_3_2 1 18 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  212)))))))))))))))))) (allB_succ 17 212 (allA_succ_of_accept 16 17 212 (accept_3_2 16 17 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 17 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 212
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 17 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 212 (accept_3_2 13 17 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 17 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 17 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 212 (accept_3_2 10 17 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 17 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 212 (accept_3_2 7 17 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  212 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 17 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 17 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 212 (accept_3_2 4 17 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 17 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  17 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 212 (accept_3_2 1 17 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 212))))))))))))))))) (allB_succ 16 212 (allA_of_3_0 16 16 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 212 (allA_succ_of_accept 14 15 212
  (Polychromatic418967fa.accept_16_14_15_4_1_3268 14 15 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 212 (accept_3_2 13 15 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 15 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 212 (accept_3_2 10 15 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 212 (Polychromatic418967fa.accept_19_9_15_3_1_12536 9 15 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 15 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 212 (accept_3_2 7 15 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  212 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 15 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 15 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 212 (accept_3_2 4 15 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 15 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  15 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 212 (accept_3_2 1 15 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 212))))))))))))))) (allB_succ 14 212 (allA_succ_of_accept 13 14
  212 (accept_3_2 13 14 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 212 2 6 7 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 212
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 14 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 212 2 5 7 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 212 (Polychromatic418967fa.accept_16_9_14_4_1_3225 9 14 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 212 2 4 7 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 212 (accept_3_2 7 14 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 212 2 3 7 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 14 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 212 2 2 7 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 212 (Polychromatic418967fa.accept_13_3_1_4_1_945 3
  14 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 212 2 1 7 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 212 (accept_3_2 1 14
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 212)))))))))))))) (allB_succ 13 212 (allA_of_3_0 13 13 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 212 (allA_succ_of_accept 11 12 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 12 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 212 2 5 6 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 212 (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 12 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 212 4 2 3 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 212 (accept_3_2 7 12 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 212 2 3 6 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 212 (Polychromatic418967fa.accept_13_5_12_4_1_449 5 12 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 212 4 1 3 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 12
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 212 2 1 6 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 212 (accept_3_2 1 12
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 212)))))))))))) (allB_succ 11 212 (allA_succ_of_accept 10 11
  212 (accept_3_2 10 11 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 212
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 11 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 11 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 212 (accept_3_2 7 11 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 11 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 5
  11 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 212 (accept_3_2 4 11 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 212
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 11 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 212 (accept_3_2 1 11 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  212))))))))))) (allB_succ 10 212 (allA_of_3_0 10 10 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 212
  (allA_succ_of_accept 8 9 212 (Polychromatic418967fa.accept_13_8_9_4_1_1552 8 9 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 212 (accept_3_2 7 9 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 212 (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 9 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 212 (accept_3_2 4 9 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 212 (Polychromatic418967fa.accept_18_3_9_14_1_2219 3
  9 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 212
  (Polychromatic418967fa.accept_20_2_9_12_1_2546 2 9 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 212 (accept_3_2 1 9 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 212)))))))))
  (allB_succ 8 212 (allA_succ_of_accept 7 8 212 (accept_3_2 7 8 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 212 2 3 4 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 8 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 212 4 1 2 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 8 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 212 2 1 4 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 212 (accept_3_2 1 8 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 212)))))))) (allB_succ 7 212 (allA_of_3_0 7 7 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 6 212 (allA_succ_of_accept 5 6 212 (Polychromatic418967fa.accept_13_5_6_4_1_1582 5 6
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 212 2 2 3 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 6 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 212 2 1 3 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 212 (accept_3_2 1 6 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 212))))))
  (allB_succ 5 212 (allA_succ_of_accept 4 5 212 (accept_3_2 4 5 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 5 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 5 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 212 (accept_3_2 1 5 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 212))))) (allB_succ 4 212 (allA_of_3_0 4 4 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 212 (allA_succ_of_accept 2 3 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 3 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 212 (accept_3_2 1 3 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 212))) (allB_succ 2 212 (allA_succ_of_accept 1 2 212 (accept_3_2 1 2 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 212)) (allB_two
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


