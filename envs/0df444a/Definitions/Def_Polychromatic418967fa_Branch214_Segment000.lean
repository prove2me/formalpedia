-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch214_Segment000
-- name    : Polychromatic418967fa_Branch214_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:34:37.243151+00:00
-- url     : https://prove2.me/theorems/01aeef34-5c81-40a2-8074-411c855a8fb1
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

def Polychromatic418967fa.branch_214_segment_000 : allB 127 214 :=
  allB_succ' 89 126 214 (Eq.refl Bool.true) (allA_succ_of_gcd 88 126 214 2 44 63 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 126 214
  (Polychromatic418967fa.accept_12_3_6_10_1_576 87 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 126 214 2 43 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 126 214 (Polychromatic418967fa.accept_10_5_6_4_1_64 85 126 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 126 214 2 42 63 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 126 214 (accept_3_3 83 126 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 126 214 2 41 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 126 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085
  81 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 126 214 2 40 63 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 126 214
  (Polychromatic418967fa.accept_13_1_9_6_1_146 79 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 214 2 39 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 214 (accept_3_3 77 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 126 214 2 38 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 126 214 (Polychromatic418967fa.accept_10_5_6_4_1_64 75 126 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 126 214 2 37 63 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 126 214
  (Polychromatic418967fa.accept_15_13_6_4_1_1221 73 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 214 2 36 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 126 214 (accept_3_3 71 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 126 214 2 35 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 126 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 69 126 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 126 214 2 34 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 126 214
  (Polychromatic418967fa.accept_13_2_9_6_1_501 67 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 214 2 33 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 214 (accept_3_3 65 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 126 214 2 32 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 126 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 126 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 126 214 2 31 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 126 214
  (Polychromatic418967fa.accept_19_4_12_5_1_8615 61 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 214 2 30 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 214 (accept_3_3 59 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 126 214 2 29 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 126 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 57 126 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 126 214 2 28 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 126 214
  (Polychromatic418967fa.accept_10_5_6_4_1_64 55 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 214 2 27 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 214 (accept_3_3 53 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 126 214 2 26 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 126 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 126 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 126 214 2 25 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 126 214
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 49 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 214 2 24 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 126 214 (accept_3_3 47 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 126 214 2 23 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 126 214 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 126 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 126 214 2 22 63 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 214
  (Polychromatic418967fa.accept_13_4_9_6_1_2376 43 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 214 2 21 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 214 (accept_3_3 41 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 126 214 2 20 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 126 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 126 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 126 214 2 19 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 214
  (Polychromatic418967fa.accept_17_3_7_10_1_3948 37 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 214 2 18 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 214 (accept_3_3 35 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 126 214 2 17 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 126 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 126 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 126 214 2 16 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 214
  (Polychromatic418967fa.accept_17_14_7_10_1_7808 31 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 126 214 2 15 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 126 214 (accept_3_3 29 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 126 214 2 14 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 126 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 126 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 126 214 2 13 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 214
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 214 2 12 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 214 (accept_3_3 23 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 126 214 2 11 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 126 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 126 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 126 214 2 10 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 214
  (Polychromatic418967fa.accept_20_19_6_14_1_3906 19 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 126 214 2 9 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 126 214 (accept_3_3 17 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 126 214 2 8 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 126 214 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 126 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 126 214 2 7 63 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 214
  (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 126 214 2 6 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 126 214 (accept_3_3 11 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 126 214 2 5 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 126 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 126 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 214 2 4 63 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 214
  (Polychromatic418967fa.accept_13_7_9_6_1_148 7 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 214 2 3 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 214 (accept_3_3 5 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126
  214 2 2 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  126 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 126 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 126 214 2 1 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 126 214 (Polychromatic418967fa.accept_13_1_9_6_1_146 1 126 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 125 214
  (Eq.refl Bool.true) (allA_of_3_1 90 125 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 91 124 214 (Eq.refl
  Bool.true) (allA_succ_of_gcd 90 124 214 2 45 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 124 214 (accept_3_3 89 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 124 214 2 44 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 124 214 (Polychromatic418967fa.accept_13_9_7_6_1_1673 87 124 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 124 214 2 43 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 124 214
  (Polychromatic418967fa.accept_7_1_5_4_1_134 85 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 124 214 2 42 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 124 214 (accept_3_3 83 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 124 214 2 41 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 124 214 (Polychromatic418967fa.accept_17_13_5_10_1_2839 81 124 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 124 214 2 40 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 124 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 79 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 124 214 2 39 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 124 214 (accept_3_3 77 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 124 214 2 38 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 124 214 (Polychromatic418967fa.accept_19_18_10_5_1_12639 75 124 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 124 214 2 37 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 124 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 73 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 124 214 2 36 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 124 214 (accept_3_3 71 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 124 214 2 35 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 124 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 124 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 124 214 2 34 62 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 124 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 67 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 124 214 2 33 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 124 214 (accept_3_3 65 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 124 214 2 32 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 124 214 (Polychromatic418967fa.accept_11_8_3_5_1_355 63 124 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 124 214 2 31 62 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 124 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 124 214 2 30 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 124 214 (accept_3_3 59 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 124 214 2 29 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 124 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 124 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 124 214 2 28 62 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 124 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 55 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 124 214 2 27 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 124 214 (accept_3_3 53 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 124 214 2 26 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 124 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 124 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 124 214 2 25 62 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 124 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 124 214 2 24 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 124 214 (accept_3_3 47 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 124 214 2 23 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 124 214 (Polychromatic418967fa.accept_19_7_10_5_1_3090 45 124 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 214 2 22 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 214
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 124 214 2 21 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 124 214 (accept_3_3 41 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 214 2 20 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 214 (Polychromatic418967fa.accept_20_19_4_14_1_8345 39 124 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 214 2 19 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 214 2 18 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 124 214 (accept_3_3 35 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 124 214 2 17 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 124 214 (Polychromatic418967fa.accept_19_14_10_5_1_3073 33 124 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 214 2 16 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 124 214 2 15 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 124 214 (accept_3_3 29 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 124 214 2 14 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 124 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 124 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 124 214 2 13 62 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 124 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 124 214 2 12 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 124 214 (accept_3_3 23 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 124 214 2 11 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 124 214 (Polychromatic418967fa.accept_19_2_10_5_1_5639 21 124 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 124 214 2 10 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 214
  (Polychromatic418967fa.accept_11_8_3_5_1_355 19 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 124 214 2 9 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 124 214 (accept_3_3 17 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 124 214 2 8 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 124 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 124 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 124 214 2 7 62 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 124 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 124 214 2 6 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 124 214 (accept_3_3 11 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 124 214 2 5 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 124 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 124 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 214 2 4 62 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 124 214 2 3 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 124 214 (accept_3_3 5 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124
  214 2 2 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  124 214 (Polychromatic418967fa.accept_19_3_10_5_1_4314 3 124 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 124 214 2 1 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 124 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 124 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 123 214
  (Eq.refl Bool.true) (allA_succ_of_accept 91 123 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 123 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 90 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 123 214 (accept_3_3 89 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 123 214 (Polychromatic418967fa.accept_19_12_9_5_1_8593 88 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 123 214 (Polychromatic418967fa.accept_10_7_3_4_1_978 87 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 123 214 (accept_3_3 86 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 123 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 123 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 84 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 123 214 (accept_3_3 83 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 123 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 123 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 123 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 123 214 (accept_3_3 80 123 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 123 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 78 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 123 214 (accept_3_3 77 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 123 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 123 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 123 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 123 214 (accept_3_3 74 123 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 123 214
  (Polychromatic418967fa.accept_19_15_9_5_1_5656 72 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 123 214 (accept_3_3 71 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 123 214 (Polychromatic418967fa.accept_19_13_9_5_1_8541 70 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 123 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 123 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 123 214 (accept_3_3 68 123 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 123 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 123 214 (accept_3_3 65 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 123 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 123 214 (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 123 214 (accept_3_3 62 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 123 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 214
  (Polychromatic418967fa.accept_18_6_15_16_1_7325 60 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 123 214 (accept_3_3 59 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 123 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 123 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 123 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 123 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 123 214 (accept_3_3 56 123 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 55
  123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 54 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 123 214 (accept_3_3 53 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 123 214 (Polychromatic418967fa.accept_11_8_2_5_1_1769 52 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 123 214 (Polychromatic418967fa.accept_16_3_11_6_1_4467 51 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 214 (accept_3_3 50 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 123 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 123 214 (accept_3_3 47 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 123 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 123 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 123 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 214 (accept_3_3 44 123 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 123 214 (accept_3_3 41 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 123 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 123 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 123 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 214 (accept_3_3 38 123 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 214
  (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 123 214 (accept_3_3 35 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 123 214 (Polychromatic418967fa.accept_16_2_11_6_1_737 34 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 123 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 123 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 123 214 (accept_3_3 32 123 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 123 214 (accept_3_3 29 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 123 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 123 214 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 214 (accept_3_3 26 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 123 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 214
  (Polychromatic418967fa.accept_18_6_15_16_1_7325 24 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 123 214 (accept_3_3 23 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 123 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 123 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 214 (accept_3_3 20 123 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 19
  123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 123 214 (accept_3_3 17 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 123 214 (Polychromatic418967fa.accept_15_1_3_4_1_1217 16 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 123 214 (Polychromatic418967fa.accept_14_1_11_4_1_3430 15 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 214 (accept_3_3 14 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 123 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 123 214 (accept_3_3 11 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 123 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 123 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 123 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 214 (accept_3_3 8 123 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 123 214 (accept_3_3 5 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  123 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 123 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 123 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 123 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 214 (accept_3_3 2 123 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 123 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 122 214
  (Eq.refl Bool.true) (allA_of_3_1 93 122 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 94 121 214 (Eq.refl
  Bool.true) (allA_succ_of_accept 93 121 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 121 214 (accept_3_3 92 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 121 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 121 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 121 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 90 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 121 214 (accept_3_3 89 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 121 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 88 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 121 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 121 214 (accept_3_3 86 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 121 214 (Polychromatic418967fa.accept_10_5_1_4_1_1444 85 121 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 121 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 84 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 121 214 (accept_3_3 83 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 121 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 82 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 121 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 121 214 (accept_3_3 80 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 121 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 121 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 121 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 78 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 121 214 (accept_3_3 77 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 121 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 121 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 121 214 (accept_3_3 74 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 121 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 121 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 121 214
  (Polychromatic418967fa.accept_13_7_4_6_1_3221 72 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 121 214 (accept_3_3 71 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 121 214 (Polychromatic418967fa.accept_13_5_4_6_1_2371 70 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 121 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 121 214 (accept_3_3 68 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 121 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 121 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 121 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 121 214 (accept_3_3 65 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 121 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 121 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 121 214 (accept_3_3 62 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 121 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 121 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 121 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 121 214 (accept_3_3 59 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 121 214 (Polychromatic418967fa.accept_14_2_9_4_1_1735 58 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 121 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 121 214 (accept_3_3 56 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 121 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 121 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 121 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 121 214 (accept_3_3 53 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 121 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 121 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 121 214 (accept_3_3 50 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 121 214 (Polychromatic418967fa.accept_13_10_4_6_1_3224 49 121 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 121 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 121 214 (accept_3_3 47 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 121 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 121 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 121 214 (accept_3_3 44 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 121 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 121 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 121 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 121 214 (accept_3_3 41 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 121 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 121 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 121 214 (accept_3_3 38 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 121 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 121 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 121 214
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 121 214 (accept_3_3 35 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 121 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 121 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 121 214 (accept_3_3 32 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 121 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 121 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 121 214 (accept_3_3 29 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 121 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 121 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 214 (accept_3_3 26 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 121 214 (Polychromatic418967fa.accept_10_5_1_4_1_1444 25 121 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 121 214 (accept_3_3 23 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 121 214 (Polychromatic418967fa.accept_13_9_4_6_1_1005 22 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 121 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 214 (accept_3_3 20 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 121 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 214
  (Polychromatic418967fa.accept_13_5_4_6_1_2371 18 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 214 (accept_3_3 17 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 214 (accept_3_3 14 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 121 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 214 (accept_3_3 11 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 214 (accept_3_3 8 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 121 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 214 (accept_3_3 5 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 121 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 214 (accept_3_3 2 121 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 121 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 120
  214 (Eq.refl Bool.true) (allA_succ_of_gcd 94 120 214 2 47 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 120 214 (Polychromatic418967fa.accept_21_9_15_4_1_2190 93 120
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 120 214 2 46 60 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 120 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 91 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 120 214 2 45 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 120 214 (accept_3_3 89 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 120 214 2 44 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 120 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 120 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 120 214 2 43 60 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 120 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 85 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 120 214 2 42 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 120 214 (accept_3_3 83 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 120 214 2 41 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 120 214 (Polychromatic418967fa.accept_11_4_10_5_1_1202 81 120 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 120 214 2 40 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 120 214
  (Polychromatic418967fa.accept_13_1_3_6_1_158 79 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 120 214 2 39 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 120 214 (accept_3_3 77 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 120 214 2 38 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 120 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 120 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 120 214 2 37 60 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 120 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 73 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 214 2 36 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 120 214 (accept_3_3 71 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 120 214 2 35 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 120 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 120 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 120 214 2 34 60 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 120 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 214 2 33 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 120 214 (accept_3_3 65 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 120 214 2 32 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 120 214 (Polychromatic418967fa.accept_18_9_12_16_1_7323 63 120 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 120 214 2 31 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 120 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 214 2 30 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 214 (accept_3_3 59 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 120 214 2 29 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 120 214 (Polychromatic418967fa.accept_13_5_3_6_1_3278 57 120 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 120 214 2 28 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 120 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 214 2 27 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 120 214 (accept_3_3 53 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 120 214 2 26 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 120 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 120 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 120 214 2 25 60 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 214 2 24 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 214 (accept_3_3 47 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 120 214 2 23 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 120 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 120 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 120 214 2 22 60 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 214
  (Polychromatic418967fa.accept_17_9_1_10_1_2859 43 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 214 2 21 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 214 (accept_3_3 41 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 214 2 20 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 120 214 (Polychromatic418967fa.accept_11_6_10_5_1_341 39 120 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 120 214 2 19 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 214 2 18 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 120 214 (accept_3_3 35 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 120 214 2 17 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 120 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 120 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 120 214 2 16 60 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 214 2 15 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 120 214 (accept_3_3 29 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 120 214 2 14 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 120 214 (Polychromatic418967fa.accept_13_1_3_6_1_158 27 120 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 214 2 13 60 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 214
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 25 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 214 2 12 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 120 214 (accept_3_3 23 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 120 214 2 11 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 120 214 (Polychromatic418967fa.accept_23_21_5_7_1_12638 21 120 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 214 2 10 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 214 2 9 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 120 214 (accept_3_3 17 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 120 214 2 8 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 120 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 120 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 214 2 7 60 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 120 214 2 6 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 120 214 (accept_3_3 11 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 214 2 5 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 120 214 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 120 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 120 214 2 4 60 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 214
  (Polychromatic418967fa.accept_17_7_1_10_1_2836 7 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 120 214 2 3 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 120 214 (accept_3_3 5 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120
  214 2 2 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  120 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 120 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 120 214 2 1 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 120 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 120 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 119
  214 (Eq.refl Bool.true) (allA_of_3_1 96 119 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 97 118 214
  (Eq.refl Bool.true) (allA_succ_of_gcd 96 118 214 2 48 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 118 214 (accept_3_3 95 118 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 94 118 214 2 47 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 93 118 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 93 118 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 118 214 2 46 59 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 118 214
  (Polychromatic418967fa.accept_11_3_8_5_1_336 91 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 118 214 2 45 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 118 214 (accept_3_3 89 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 118 214 2 44 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 118 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 118 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 118 214 2 43 59 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 118 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 85 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 118 214 2 42 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 118 214 (accept_3_3 83 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 118 214 2 41 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 118 214 (Polychromatic418967fa.accept_13_3_1_6_1_509 81 118 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 118 214 2 40 59 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 118 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 79 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 118 214 2 39 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 118 214 (accept_3_3 77 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 118 214 2 38 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 118 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 118 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 118 214 2 37 59 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 118 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 73 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 118 214 2 36 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 118 214 (accept_3_3 71 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 118 214 2 35 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 118 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 118 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 118 214 2 34 59 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 118 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 67 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 118 214 2 33 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 118 214 (accept_3_3 65 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 118 214 2 32 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 118 214 (Polychromatic418967fa.accept_19_6_4_5_1_5650 63 118 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 118 214 2 31 59 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 118 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 61 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 118 214 2 30 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 118 214 (accept_3_3 59 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 118 214 2 29 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 118 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 118 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 118 214 2 28 59 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 118 214
  (Polychromatic418967fa.accept_13_3_1_6_1_509 55 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 118 214 2 27 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 118 214 (accept_3_3 53 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 118 214 2 26 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 118 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 118 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 118 214 2 25 59 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 118 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 118 214 2 24 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 118 214 (accept_3_3 47 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 118 214 2 23 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 118 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 118 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 214 2 22 59 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 214
  (Polychromatic418967fa.accept_17_9_16_10_1_362 43 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 214 2 21 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 214 (accept_3_3 41 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 214 2 20 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 118 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 214 2 19 59 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 214 2 18 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 214 (accept_3_3 35 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 214 2 17 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 118 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 214 2 16 59 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 214 2 15 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 214 (accept_3_3 29 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 214 2 14 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 214 (Polychromatic418967fa.accept_19_8_4_5_1_8569 27 118 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 214 2 13 59 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 214
  (Polychromatic418967fa.accept_11_3_8_5_1_336 25 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 214 2 12 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 214 (accept_3_3 23 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 214 2 11 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 118 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 214 2 10 59 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 214 2 9 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 118 214 (accept_3_3 17 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 118 214 2 8 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 118 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 118 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 118 214 2 7 59 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 118 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 118 214 2 6 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 118 214 (accept_3_3 11 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 118 214 2 5 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 118 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 118 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 118 214 2 4 59 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 118 214
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 118 214 2 3 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 118 214 (accept_3_3 5 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 118
  214 2 2 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  118 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 118 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 118 214 2 1 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 118 214 (Polychromatic418967fa.accept_18_1_10_16_1_566 1 118 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  117 214 (Eq.refl Bool.true) (allA_succ_of_accept 97 117 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 117 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 214
  (Polychromatic418967fa.accept_19_1_3_5_1_3092 96 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 117 214 (accept_3_3 95 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 117 214 (Polychromatic418967fa.accept_29_7_1_11_1_12637 94 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 117 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 93 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 117 214 (accept_3_3 92 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 117 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 90 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 117 214 (accept_3_3 89 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 117 214 (Polychromatic418967fa.accept_24_16_21_22_1_12636 88 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 214 (accept_3_3 86 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 117 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 214
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 84 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 117 214 (accept_3_3 83 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 117 214 (Polychromatic418967fa.accept_10_2_7_4_1_967 82 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 117 214 (Polychromatic418967fa.accept_10_1_7_4_1_968 81 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 214 (accept_3_3 80 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 117 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 214
  (Polychromatic418967fa.accept_7_1_5_4_1_134 78 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 117 214 (accept_3_3 77 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 117 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 117 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 214 (accept_3_3 74 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 72 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 117 214 (accept_3_3 71 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 117 214 (Polychromatic418967fa.accept_17_2_15_10_1_5171 70 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 117 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 214 (accept_3_3 68 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 66 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 117 214 (accept_3_3 65 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 117 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 117 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 214 (accept_3_3 62 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 214
  (Polychromatic418967fa.accept_21_18_12_4_1_4967 60 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 117 214 (accept_3_3 59 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 117 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 117 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 214 (accept_3_3 56 117 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 54 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 117 214 (accept_3_3 53 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 117 214 (Polychromatic418967fa.accept_10_2_7_4_1_967 52 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 117 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 214 (accept_3_3 50 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 117 214 (accept_3_3 47 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 117 214 (Polychromatic418967fa.accept_15_1_12_4_1_2022 46 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 117 214 (Polychromatic418967fa.accept_19_7_3_5_1_8585 45 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 214 (accept_3_3 44 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 117 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 214
  (Polychromatic418967fa.accept_10_2_7_4_1_967 42 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 117 214 (accept_3_3 41 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 117 214 (Polychromatic418967fa.accept_19_2_3_5_1_5721 40 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 117 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 214 (accept_3_3 38 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 214
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 117 214 (accept_3_3 35 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 117 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 117 214 (Polychromatic418967fa.accept_10_3_7_4_1_584 33 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 214 (accept_3_3 32 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 117 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 117 214 (accept_3_3 29 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 117 214 (Polychromatic418967fa.accept_21_7_12_4_1_6493 28 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 117 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 214 (accept_3_3 26 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 214
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 24 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 117 214 (accept_3_3 23 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 117 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 117 214 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 214 (accept_3_3 20 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 117 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 117 214 (accept_3_3 17 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 117 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 214 (accept_3_3 14 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 214
  (Polychromatic418967fa.accept_10_2_7_4_1_967 12 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 117 214 (accept_3_3 11 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 117 214 (Polychromatic418967fa.accept_19_10_3_5_1_11346 10 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 117 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 214 (accept_3_3 8 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 214 (accept_3_3 5 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 214 (Polychromatic418967fa.accept_16_4_5_6_1_8071 4 117 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 214 (accept_3_3 2 117 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 117 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  116 214 (Eq.refl Bool.true) (allA_of_3_1 99 116 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 100 115 214
  (Eq.refl Bool.true) (allA_succ_of_accept 99 115 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 99 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 115 214 (accept_3_3 98 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 115 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 115 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 115 214
  (Polychromatic418967fa.accept_10_6_5_4_1_571 96 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 115 214 (accept_3_3 95 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 115 214 (Polychromatic418967fa.accept_17_9_13_10_1_1825 94 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 115 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 115 214 (accept_3_3 92 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 115 214 (Polychromatic418967fa.accept_10_1_5_4_1_276 91 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 115 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 90 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 115 214 (accept_3_3 89 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 115 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 88 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 115 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 115 214 (accept_3_3 86 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 115 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 115 214
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 84 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 115 214 (accept_3_3 83 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 115 214 (Polychromatic418967fa.accept_13_4_11_6_1_1033 82 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 115 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 115 214 (accept_3_3 80 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 115 214 (Polychromatic418967fa.accept_10_9_5_4_1_966 79 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 115 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 78 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 115 214 (accept_3_3 77 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 115 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 115 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 115 214 (accept_3_3 74 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 115 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 115 214
  (Polychromatic418967fa.accept_19_15_1_5_1_3013 72 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 115 214 (accept_3_3 71 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 115 214 (Polychromatic418967fa.accept_13_5_11_6_1_505 70 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 115 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 115 214 (accept_3_3 68 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 115 214 (Polychromatic418967fa.accept_15_7_10_4_1_151 67 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 115 214
  (Polychromatic418967fa.accept_10_6_5_4_1_571 66 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 115 214 (accept_3_3 65 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 115 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 115 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 214 (accept_3_3 62 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 115 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 115 214
  (Polychromatic418967fa.accept_13_8_11_6_1_1035 60 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 115 214 (accept_3_3 59 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 115 214 (Polychromatic418967fa.accept_15_13_10_4_1_1232 58 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 115 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 214 (accept_3_3 56 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 115 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 115 214
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 54 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 115 214 (accept_3_3 53 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 115 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 115 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 214 (accept_3_3 50 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 115 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 115 214 (accept_3_3 47 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 115 214 (Polychromatic418967fa.accept_10_6_5_4_1_571 46 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 115 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 214 (accept_3_3 44 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 214
  (Polychromatic418967fa.accept_19_4_1_5_1_9933 42 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 115 214 (accept_3_3 41 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 115 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 115 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 214 (accept_3_3 38 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 115 214 (accept_3_3 35 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 115 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 115 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 214 (accept_3_3 32 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 214 (Polychromatic418967fa.accept_10_1_5_4_1_276 31 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 214
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 30 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 115 214 (accept_3_3 29 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 115 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 115 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 214 (accept_3_3 26 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 214
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 24 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 214 (accept_3_3 23 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 214 (accept_3_3 20 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 214 (Polychromatic418967fa.accept_10_9_5_4_1_966 19 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 214
  (Polychromatic418967fa.accept_13_5_11_6_1_505 18 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 214 (accept_3_3 17 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 214 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 214 (accept_3_3 14 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 214
  (Polychromatic418967fa.accept_19_12_1_5_1_9924 12 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 214 (accept_3_3 11 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 214 (Polychromatic418967fa.accept_20_10_15_14_1_6797 10 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 214 (accept_3_3 8 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 214 (Polychromatic418967fa.accept_14_7_3_4_1_1816 7 115 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 214 (accept_3_3 5 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 115 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 214 (accept_3_3 2 115 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 115 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 114 214 (Eq.refl Bool.true) (allA_succ_of_gcd 100 114 214 2 50 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 114 214 (Polychromatic418967fa.accept_12_3_6_10_1_576
  99 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 114 214 2 49 57 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 114 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 97 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 114 214 2 48 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 114 214 (accept_3_3 95 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 114 214 2 47 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 114 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 93 114 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 114 214 2 46 57 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 114 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 91 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 214 2 45 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 214 (accept_3_3 89 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 114 214 2 44 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 114 214 (Polychromatic418967fa.accept_11_10_4_5_1_359 87 114 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 114 214 2 43 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 114 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 85 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 214 2 42 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 214 (accept_3_3 83 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 114 214 2 41 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 114 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 81 114 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 114 214 2 40 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 114 214
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 79 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 214 2 39 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 214 (accept_3_3 77 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 114 214 2 38 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 114 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 114 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 114 214 2 37 57 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 114 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 73 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 214 2 36 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 214 (accept_3_3 71 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 114 214 2 35 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 114 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 114 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 114 214 2 34 57 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 114 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 67 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 214 2 33 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 214 (accept_3_3 65 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 114 214 2 32 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 114 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 114 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 114 214 2 31 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 114 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 61 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 214 2 30 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 214 (accept_3_3 59 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 114 214 2 29 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 114 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 114 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 114 214 2 28 57 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 214 2 27 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 214 (accept_3_3 53 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 114 214 2 26 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 114 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 114 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 114 214 2 25 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 214 2 24 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 214 (accept_3_3 47 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 114 214 2 23 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 114 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 114 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 114 214 2 22 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 214
  (Polychromatic418967fa.accept_11_10_4_5_1_359 43 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 214 2 21 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 214 (accept_3_3 41 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 114 214 2 20 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 114 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 114 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 114 214 2 19 57 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 214 2 18 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 214 (accept_3_3 35 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 114 214 2 17 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 114 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 114 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 114 214 2 16 57 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 214 2 15 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 214 (accept_3_3 29 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 114 214 2 14 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 114 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 114 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 114 214 2 13 57 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 214
  (Polychromatic418967fa.accept_13_12_10_6_1_3212 25 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 114 214 2 12 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 114 214 (accept_3_3 23 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 114 214 2 11 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 114 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 114 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 114 214 2 10 57 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 214 2 9 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 114 214 (accept_3_3 17 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 114 214 2 8 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 114 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 114 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 114 214 2 7 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 214 2 6 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 114 214 (accept_3_3 11 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 114 214 2 5 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 114 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 114 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 114 214 2 4 57 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 214
  (Polychromatic418967fa.accept_31_7_21_28_1_12635 7 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 114 214 2 3 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 114 214 (accept_3_3 5 114 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 114 214 2 2 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 114 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 114 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 214 2 1 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  114 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 113 214 (Eq.refl Bool.true) (allA_of_3_1 102 113 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 103 112
  214 (Eq.refl Bool.true) (allA_succ_of_gcd 102 112 214 2 51 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 112 214 (accept_3_3 101 112 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 112 214 2 50 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 112 214 (Polychromatic418967fa.accept_22_11_2_16_1_759 99 112 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 112 214 2 49 56 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 112 214
  (Polychromatic418967fa.accept_10_7_2_4_1_569 97 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 112 214 2 48 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 112 214 (accept_3_3 95 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 112 214 2 47 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 112 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 93 112 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 112 214 2 46 56 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 112 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 91 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 112 214 2 45 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 112 214 (accept_3_3 89 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 112 214 2 44 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 112 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 87 112 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 112 214 2 43 56 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 112 214
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 85 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 112 214 2 42 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 112 214 (accept_3_3 83 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 112 214 2 41 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 112 214 (Polychromatic418967fa.accept_21_18_7_4_1_8131 81 112 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 112 214 2 40 56 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 112 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 79 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 112 214 2 39 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 112 214 (accept_3_3 77 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 112 214 2 38 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 112 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 75 112 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 112 214 2 37 56 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 112 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 73 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 112 214 2 36 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 112 214 (accept_3_3 71 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 112 214 2 35 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 112 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 112 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 112 214 2 34 56 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 112 214
  (Polychromatic418967fa.accept_10_7_2_4_1_569 67 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 112 214 2 33 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 112 214 (accept_3_3 65 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 112 214 2 32 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 112 214 (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 112 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 112 214 2 31 56 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 112 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 112 214 2 30 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 112 214 (accept_3_3 59 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 112 214 2 29 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 112 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 112 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 112 214 2 28 56 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 112 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 112 214 2 27 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 112 214 (accept_3_3 53 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 112 214 2 26 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 112 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 112 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 112 214 2 25 56 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 112 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 112 214 2 24 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 112 214 (accept_3_3 47 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 112 214 2 23 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 112 214 (Polychromatic418967fa.accept_19_7_17_5_1_3081 45 112 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 112 214 2 22 56 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 112 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 112 214 2 21 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 112 214 (accept_3_3 41 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 112 214 2 20 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 112 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 112 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 112 214 2 19 56 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 112 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 112 214 2 18 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 112 214 (accept_3_3 35 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 112 214 2 17 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 112 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 112 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 112 214 2 16 56 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 112 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 112 214 2 15 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 112 214 (accept_3_3 29 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 112 214 2 14 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 112 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 112 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 214 2 13 56 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 214 2 12 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 112 214 (accept_3_3 23 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 112 214 2 11 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 112 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 112 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 214 2 10 56 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 214 2 9 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 112 214 (accept_3_3 17 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 112 214 2 8 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 112 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 112 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 112 214 2 7 56 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 112 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 112 214 2 6 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 112 214 (accept_3_3 11 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 112 214 2 5 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 112 214 (Polychromatic418967fa.accept_22_9_2_16_1_6152 9 112 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 112 214 2 4 56 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 112 214
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 112 214 2 3 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 112 214 (accept_3_3 5 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112
  214 2 2 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  112 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 112 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 112 214 2 1 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 112 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 112 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 111 214 (Eq.refl Bool.true) (allA_succ_of_accept 103 111 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 111 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 102 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 111 214 (accept_3_3 101 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 111 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 100 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 111 214 (Polychromatic418967fa.accept_15_9_6_4_1_1220 99 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 111 214 (accept_3_3 98 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 111 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 96 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 111 214 (accept_3_3 95 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 111 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 94 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 111 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 111 214 (accept_3_3 92 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 90 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 111 214 (accept_3_3 89 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 111 214 (Polychromatic418967fa.accept_15_13_6_4_1_1221 88 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 111 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 111 214 (accept_3_3 86 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 214
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 84 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 111 214 (accept_3_3 83 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 111 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 82 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 111 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 111 214 (accept_3_3 80 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 214
  (Polychromatic418967fa.accept_9_6_3_7_1_580 78 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 111 214 (accept_3_3 77 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 111 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 111 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 214 (accept_3_3 74 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 111 214 (accept_3_3 71 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 111 214 (Polychromatic418967fa.accept_15_10_6_4_1_1256 70 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 111 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 214 (accept_3_3 68 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 66 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 111 214 (accept_3_3 65 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 111 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 111 214 (Polychromatic418967fa.accept_20_3_11_14_1_5319 63 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 214 (accept_3_3 62 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 111 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 214
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 111 214 (accept_3_3 59 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 111 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 111 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 214 (accept_3_3 56 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 111 214 (accept_3_3 53 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 111 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 111 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 214 (accept_3_3 50 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 214
  (Polychromatic418967fa.accept_13_9_7_6_1_1673 48 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 111 214 (accept_3_3 47 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 111 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 111 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 214 (accept_3_3 44 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 214
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 111 214 (accept_3_3 41 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 111 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 214 (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 214 (accept_3_3 38 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 111 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 214
  (Polychromatic418967fa.accept_21_15_6_4_1_4990 36 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 111 214 (accept_3_3 35 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 111 214 (Polychromatic418967fa.accept_21_13_6_4_1_2178 34 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 111 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 214 (accept_3_3 32 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 214 (accept_3_3 29 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 111 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 214 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 214 (accept_3_3 26 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 111 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 214 (accept_3_3 23 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 111 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 214 (accept_3_3 20 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 214 (accept_3_3 17 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 214 (accept_3_3 14 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 111 214 (accept_3_3 11 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 111 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 111 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 214 (accept_3_3 8 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 214
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 111 214 (accept_3_3 5 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  111 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 111 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 111 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 214 (accept_3_3 2 111 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 110 214 (Eq.refl Bool.true) (allA_of_3_1 105 110 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 106 109 214 (Eq.refl Bool.true) (allA_succ_of_accept 105 109 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 214 (accept_3_3 104 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 109 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 102 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 214 (accept_3_3 101 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 100 109
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 214 (accept_3_3 98 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 214 (Polychromatic418967fa.accept_18_7_1_16_1_578 97 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 96 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 214 (accept_3_3 95 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 94 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 214 (accept_3_3 92 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 109 214 (Polychromatic418967fa.accept_13_12_5_6_1_1050 90 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 214 (accept_3_3 89 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 214 (Polychromatic418967fa.accept_10_8_9_4_1_961 88 109
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 109 214 (accept_3_3 86 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 109 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 109 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 84 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 214 (accept_3_3 83 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 214 (Polychromatic418967fa.accept_13_4_5_6_1_3201 82 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 109 214 (accept_3_3 80 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 109 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 109 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 78 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 214 (accept_3_3 77 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 214 (accept_3_3 74 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 214 (Polychromatic418967fa.accept_10_3_9_4_1_960 73 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 109 214 (Polychromatic418967fa.accept_11_6_10_5_1_341 72 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 214 (accept_3_3 71 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 214 (Polychromatic418967fa.accept_11_4_10_5_1_1202 70 109
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 214 (accept_3_3 68 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 66 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 214 (accept_3_3 65 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 64 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 214 (accept_3_3 62 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 214 (Polychromatic418967fa.accept_11_6_10_5_1_341 61 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 214 (accept_3_3 59 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 214 (accept_3_3 56 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 214 (Polychromatic418967fa.accept_17_3_7_10_1_3948 54 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 214 (accept_3_3 53 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 109
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 214 (accept_3_3 50 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 214 (accept_3_3 47 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 214 (Polychromatic418967fa.accept_18_10_1_16_1_579 46 109 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 214 (accept_3_3 44 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 214 (accept_3_3 41 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 214 (accept_3_3 38 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 214 (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 214 (Polychromatic418967fa.accept_13_10_5_6_1_1671 36 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 214 (accept_3_3 35 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 214 (Polychromatic418967fa.accept_23_11_17_7_1_12634 34
  109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 214 (accept_3_3 32 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 214 (accept_3_3 29 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 214 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 214 (accept_3_3 26 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 214 (Polychromatic418967fa.accept_10_5_9_4_1_1420 25 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 214 (accept_3_3 23 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 214 (accept_3_3 20 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 214 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 214 (accept_3_3 17 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 109
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 214 (accept_3_3 14 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 214 (accept_3_3 11 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 214 (Polychromatic418967fa.accept_13_10_5_6_1_1671 10 109 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 214 (accept_3_3 8 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 214 (accept_3_3 5 109 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 109 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 214 (accept_3_3 2 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 214 (Polychromatic418967fa.accept_13_1_5_6_1_1048 1 109 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 108 214 (Eq.refl Bool.true) (allA_succ_of_gcd 106 108 214 2 53 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 108 214
  (Polychromatic418967fa.accept_14_7_10_4_1_130 105 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 108 214 2 52 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 108 214 (Polychromatic418967fa.accept_19_8_13_5_1_1889 103 108 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 108 214 2 51 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 108 214 (accept_3_3 101 108 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 108 214 2 50 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 108 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 99 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 108 214 2 49 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 108 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 97 108 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 108 214 2 48 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 108 214 (accept_3_3 95 108 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 108 214 2 47 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 108 214 (Polychromatic418967fa.accept_13_2_4_6_1_2356
  93 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 108 214 2 46 54 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 108 214
  (Polychromatic418967fa.accept_14_7_10_4_1_130 91 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 108 214 2 45 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 108 214 (accept_3_3 89 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 108 214 2 44 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 108 214 (Polychromatic418967fa.accept_13_9_4_6_1_1005 87 108 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 108 214 2 43 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 108 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 85 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 214 2 42 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 214 (accept_3_3 83 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 108 214 2 41 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 108 214 (Polychromatic418967fa.accept_21_18_3_4_1_5013 81 108 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 108 214 2 40 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 108 214
  (Polychromatic418967fa.accept_10_9_8_4_1_970 79 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 214 2 39 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 214 (accept_3_3 77 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 108 214 2 38 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 108 214 (Polychromatic418967fa.accept_13_10_4_6_1_3224 75 108 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 108 214 2 37 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 108 214
  (Polychromatic418967fa.accept_11_7_9_5_1_338 73 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 214 2 36 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 214 (accept_3_3 71 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 108 214 2 35 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 108 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 108 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 108 214 2 34 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 214
  (Polychromatic418967fa.accept_13_2_4_6_1_2356 67 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 214 2 33 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 214 (accept_3_3 65 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 108 214 2 32 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 108 214 (Polychromatic418967fa.accept_13_11_4_6_1_1006 63 108 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 108 214 2 31 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 214
  (Polychromatic418967fa.accept_13_9_4_6_1_1005 61 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 214 2 30 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 214 (accept_3_3 59 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 108 214 2 29 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 108 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 108 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 108 214 2 28 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 55 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 214 2 27 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 214 (accept_3_3 53 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 108 214 2 26 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 108 214 (Polychromatic418967fa.accept_11_7_9_5_1_338 51 108 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 108 214 2 25 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 214
  (Polychromatic418967fa.accept_10_9_8_4_1_970 49 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 214 2 24 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 214 (accept_3_3 47 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 108 214 2 23 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 108 214 (Polychromatic418967fa.accept_19_7_13_5_1_7125 45 108 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 108 214 2 22 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 214 2 21 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 214 (accept_3_3 41 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 108 214 2 20 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 108 214 (Polychromatic418967fa.accept_10_9_8_4_1_970 39 108 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 108 214 2 19 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 214
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 37 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 214 2 18 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 108 214 (accept_3_3 35 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 108 214 2 17 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 108 214 (Polychromatic418967fa.accept_13_7_4_6_1_3221 33 108 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 214 2 16 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 214
  (Polychromatic418967fa.accept_13_5_4_6_1_2371 31 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 214 2 15 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 214 (accept_3_3 29 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 214 2 14 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 108 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 108 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 214 2 13 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 214
  (Polychromatic418967fa.accept_20_5_8_14_1_5341 25 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 214 2 12 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 108 214 (accept_3_3 23 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 108 214 2 11 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 108 214 (Polychromatic418967fa.accept_14_7_10_4_1_130 21 108 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 108 214 2 10 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 214
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 214 2 9 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 108 214 (accept_3_3 17 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 108 214 2 8 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 108 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 108 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 214 2 7 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 214 2 6 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 108 214 (accept_3_3 11 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 108 214 2 5 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 108 214 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 108 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 214 2 4 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 214
  (Polychromatic418967fa.accept_11_7_9_5_1_338 7 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 108 214 2 3 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 108 214 (accept_3_3 5 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108
  214 2 2 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  108 214 (Polychromatic418967fa.accept_20_3_8_14_1_5342 3 108 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 108 214 2 1 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 108 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 108 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 214 (allA_of_3_1 107 107 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 106 214
  (allA_succ_of_accept 105 106 214 (Polychromatic418967fa.accept_10_5_6_4_1_64 105 106 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 106 214 2 52 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 106 214 (Polychromatic418967fa.accept_7_5_1_4_1_122
  103 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 106 214 2 51 53 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 106 214
  (accept_3_3 101 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 106 214 2 50 53 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 106 214
  (Polychromatic418967fa.accept_13_8_2_6_1_2385 99 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 106 214 2 49 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 106 214 (Polychromatic418967fa.accept_11_9_7_5_1_749 97 106 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 106 214 2 48 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 106 214 (accept_3_3 95 106 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 106 214 2 47 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 106 214 (Polychromatic418967fa.accept_15_3_1_4_1_1246
  93 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 106 214 2 46 53 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 106 214
  (Polychromatic418967fa.accept_17_6_4_10_1_5176 91 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 106 214 2 45 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 106 214 (accept_3_3 89 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 106 214 2 44 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 106 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 106 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 106 214 2 43 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 106 214
  (Polychromatic418967fa.accept_10_5_6_4_1_64 85 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 106 214 2 42 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 106 214 (accept_3_3 83 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 106 214 2 41 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 106 214 (Polychromatic418967fa.accept_14_11_8_4_1_2628 81 106 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 106 214 2 40 53 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 106 214
  (Polychromatic418967fa.accept_13_1_2_6_1_515 79 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 106 214 2 39 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 106 214 (accept_3_3 77 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 106 214 2 38 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 106 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 106 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 106 214 2 37 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 106 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 73 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 106 214 2 36 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 106 214 (accept_3_3 71 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 106 214 2 35 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 106 214 (Polychromatic418967fa.accept_13_4_2_6_1_1043 69 106 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 106 214 2 34 53 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 106 214
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 67 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 106 214 2 33 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 106 214 (accept_3_3 65 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 106 214 2 32 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 106 214 (Polychromatic418967fa.accept_15_3_1_4_1_1246 63 106 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 214 2 31 53 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 106 214 2 30 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 106 214 (accept_3_3 59 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 214 2 29 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 214 (Polychromatic418967fa.accept_15_12_1_4_1_2899 57 106 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 214 2 28 53 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 214
  (Polychromatic418967fa.accept_10_5_6_4_1_64 55 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 106 214 2 27 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 214 (accept_3_3 53 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 214 2 26 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 214 (Polychromatic418967fa.accept_13_12_2_6_1_2396 51 106 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 214 2 25 53 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 214
  (Polychromatic418967fa.accept_13_10_2_6_1_1044 49 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 214 2 24 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 214 (accept_3_3 47 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 214 2 23 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 106 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 214 2 22 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 214
  (Polychromatic418967fa.accept_13_4_2_6_1_1043 43 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 214 2 21 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 214 (accept_3_3 41 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 214 2 20 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 214 (Polychromatic418967fa.accept_14_11_8_4_1_2628 39 106 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 214 2 19 53 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 214
  (Polychromatic418967fa.accept_28_9_22_18_1_12633 37 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 106 214 2 18 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 106 214 (accept_3_3 35 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 214 2 17 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 106 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 214 2 16 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 214 2 15 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 214 (accept_3_3 29 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 214 2 14 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 214 (Polychromatic418967fa.accept_13_1_2_6_1_515 27 106 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 214 2 13 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 214
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 214 2 12 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 214 (accept_3_3 23 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 214 2 11 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 214 (Polychromatic418967fa.accept_13_8_2_6_1_2385 21 106 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 214 2 10 53 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 214 2 9 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 106 214 (accept_3_3 17 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 106 214 2 8 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 106 214 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 106 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 106 214 2 7 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 106 214
  (Polychromatic418967fa.accept_19_13_11_5_1_5692 13 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 106 214 2 6 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 106 214 (accept_3_3 11 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 106 214 2 5 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 106 214 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 106 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 106 214 2 4 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 106 214
  (Polychromatic418967fa.accept_21_7_1_4_1_4985 7 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 106 214 2 3 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 106 214 (accept_3_3 5 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 106
  214 2 2 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  106 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 106 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 106 214 2 1 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 106 214 (Polychromatic418967fa.accept_13_1_2_6_1_515 1 106 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 214 (allA_succ_of_accept 104 105 214 (accept_3_3 104 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 105 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 102 105
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 214 (accept_3_3 101 105
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 105 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 100 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 105 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 105 214 (accept_3_3 98 105 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 105 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 214 (Polychromatic418967fa.accept_10_6_5_4_1_571
  96 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 214 (accept_3_3 95
  105 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 105 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 94 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 105 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 93 105 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 214 (accept_3_3 92 105 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 214 (Polychromatic418967fa.accept_12_6_9_10_1_565
  90 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 214 (accept_3_3 89
  105 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 214
  (Polychromatic418967fa.accept_20_8_5_14_1_3904 88 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 105 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 105 214 (accept_3_3 86 105 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 105 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 214 (Polychromatic418967fa.accept_9_3_6_7_1_562
  84 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 214 (accept_3_3 83
  105 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 105 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 82 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 105 214 (Polychromatic418967fa.accept_10_1_5_4_1_276 81 105 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 105 214 (accept_3_3 80 105 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 214 (Polychromatic418967fa.accept_11_1_6_5_1_1732
  78 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 214 (accept_3_3 77
  105 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 105 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 76 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 105 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 105 214 (accept_3_3 74 105 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 105 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 214 (Polychromatic418967fa.accept_13_7_1_6_1_3287
  72 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 214 (accept_3_3 71
  105 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 105 214
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 70 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 105 214 (Polychromatic418967fa.accept_10_9_5_4_1_966 69 105 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 214 (accept_3_3 68 105 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 214 (Polychromatic418967fa.accept_9_3_6_7_1_562
  66 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 214 (accept_3_3 65
  105 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 64 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 105 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 214 (accept_3_3 62 105 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 105 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 214 (Polychromatic418967fa.accept_13_8_1_6_1_997
  60 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 214 (accept_3_3 59
  105 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 58 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 105 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 105 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 214 (accept_3_3 56 105 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 214
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 214 (accept_3_3 53 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 105 214 (Polychromatic418967fa.accept_14_10_7_4_1_3453 52 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 214 (accept_3_3 50 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 105 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 105 214 (accept_3_3 47 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 105 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 105 214 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 105 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 214 (accept_3_3 44 105 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 105 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 42 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 105 214 (accept_3_3 41 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 105 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 214 (accept_3_3 38 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 105 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 214
  (Polychromatic418967fa.accept_10_6_5_4_1_571 36 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 105 214 (accept_3_3 35 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 105 214 (Polychromatic418967fa.accept_11_1_6_5_1_1732 34 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 105 214 (Polychromatic418967fa.accept_13_7_1_6_1_3287 33 105 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 214 (accept_3_3 32 105 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 105 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 105 214 (accept_3_3 29 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 105 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 214 (accept_3_3 26 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 105 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 214
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 214 (accept_3_3 23 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 105 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 105 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 214 (accept_3_3 20 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 105 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 105 214 (accept_3_3 17 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 105 214 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 214 (accept_3_3 14 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 105 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 214 (accept_3_3 11 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 105 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 105 214 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 214 (accept_3_3 8 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 105 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 214
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 105 214 (accept_3_3 5 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  105 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 105 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 105 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 214 (accept_3_3 2 105 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 105 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 214 (allA_of_3_1 104 104 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 103 214
  (allA_succ_of_accept 102 103 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 102 103 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 214 (accept_3_3 101 103 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 103 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 100 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 214 (accept_3_3 98 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 96 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 214 (accept_3_3 95 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 214 (Polychromatic418967fa.accept_17_9_1_10_1_2859 94 103 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 214 (accept_3_3 92 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 90 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 214 (accept_3_3 89 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 88 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 214 (accept_3_3 86 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 84 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 214 (accept_3_3 83 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 214 (accept_3_3 80 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 79 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 214 (accept_3_3 77 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 214 (accept_3_3 74 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 214 (accept_3_3 71 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 214 (Polychromatic418967fa.accept_13_5_12_6_1_508 70 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 214 (accept_3_3 68 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 214 (Polychromatic418967fa.accept_10_7_3_4_1_978 67 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 66 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 214 (accept_3_3 65 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 103 214 (accept_3_3 62 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 103 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 103 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 214 (accept_3_3 59 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 214 (accept_3_3 56 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 214 (Polychromatic418967fa.accept_11_10_4_5_1_359 54 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 214 (accept_3_3 53 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 103
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 214 (accept_3_3 50 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 214 (accept_3_3 47 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 214 (accept_3_3 44 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 214 (accept_3_3 41 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 214 (accept_3_3 38 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 214 (accept_3_3 35 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 214 (accept_3_3 32 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 214 (Polychromatic418967fa.accept_13_5_12_6_1_508 31 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 214 (accept_3_3 29 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 214 (accept_3_3 26 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 214 (accept_3_3 23 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 214 (accept_3_3 20 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 214 (Polychromatic418967fa.accept_13_5_12_6_1_508 18 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 214 (accept_3_3 17 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 103 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 214 (accept_3_3 14 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 214 (accept_3_3 11 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 214 (accept_3_3 8 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 214 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 214 (accept_3_3 5 103 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 103 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 214 (accept_3_3 2 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 103 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 214 (allA_succ_of_accept 101 102 214 (accept_3_3 101 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 102 214 2 50 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 102 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 99 102 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 102 214 2 49 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 214
  (Polychromatic418967fa.accept_10_7_2_4_1_569 97 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 102 214 2 48 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 102 214 (accept_3_3 95 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 102 214 2 47 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 102 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 93 102 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 102 214 2 46 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 91 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 102 214 2 45 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 102 214 (accept_3_3 89 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 102 214 2 44 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 102 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 87 102 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 102 214 2 43 51 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 102 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 85 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 214 2 42 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 214 (accept_3_3 83 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 102 214 2 41 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 102 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 81 102 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 102 214 2 40 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 102 214
  (Polychromatic418967fa.accept_19_3_7_5_1_12632 79 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 214 2 39 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 214 (accept_3_3 77 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 102 214 2 38 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 102 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 75 102 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 102 214 2 37 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 102 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 214 2 36 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 214 (accept_3_3 71 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 102 214 2 35 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 102 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 102 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 102 214 2 34 51 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 214 2 33 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 214 (accept_3_3 65 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 102 214 2 32 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 102 214 (Polychromatic418967fa.accept_11_8_3_5_1_355 63 102 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 102 214 2 31 51 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 214
  (Polychromatic418967fa.accept_15_1_12_4_1_2022 61 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 214 2 30 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 214 (accept_3_3 59 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 102 214 2 29 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 102 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 57 102 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 102 214 2 28 51 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 214 2 27 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 214 (accept_3_3 53 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 102 214 2 26 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 102 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 102 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 102 214 2 25 51 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 214 2 24 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 214 (accept_3_3 47 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 102 214 2 23 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 102 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 102 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 102 214 2 22 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 214
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 43 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 214 2 21 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 214 (accept_3_3 41 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 102 214 2 20 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 102 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 102 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 102 214 2 19 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 214 2 18 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 214 (accept_3_3 35 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 102 214 2 17 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 102 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 102 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 102 214 2 16 51 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 214 2 15 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 214 (accept_3_3 29 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 102 214 2 14 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 102 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 102 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 102 214 2 13 51 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 214
  (Polychromatic418967fa.accept_19_6_7_5_1_256 25 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 214 2 12 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 214 (accept_3_3 23 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 102 214 2 11 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 102 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 102 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 214 2 10 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 214 2 9 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 102 214 (accept_3_3 17 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 102 214 2 8 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 102 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 102 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 214 2 7 51 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 214 2 6 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 102 214 (accept_3_3 11 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 214 2 5 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 102 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 102 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 214 2 4 51 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 214
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 102 214 2 3 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 102 214 (accept_3_3 5 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102
  214 2 2 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  102 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 102 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 102 214 2 1 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 102 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 102 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 214 (allA_of_3_1 101 101 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 100 214 (allA_succ_of_accept 99
  100 214 (Polychromatic418967fa.accept_15_9_10_4_1_2055 99 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 100 214 2 49 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 100 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 97 100 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 100 214 2 48 50 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 100 214 (accept_3_3 95 100 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 100 214 2 47 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 100 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 93 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 100 214 2 46 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 100 214 (Polychromatic418967fa.accept_12_7_4_10_1_572 91 100 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 100 214 2 45 50 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 100 214 (accept_3_3 89 100 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 100 214 2 44 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 100 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 87 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 100 214 2 43 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 100 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 100 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 100 214 2 42 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 100 214 (accept_3_3 83 100 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 100 214 2 41 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 100 214 (Polychromatic418967fa.accept_13_3_9_6_1_502
  81 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 100 214 2 40 50 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 100 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 79 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 100 214 2 39 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 100 214 (accept_3_3 77 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 100 214 2 38 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 100 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 100 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 100 214 2 37 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 100 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 73 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 100 214 2 36 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 100 214 (accept_3_3 71 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 100 214 2 35 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 100 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 100 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 100 214 2 34 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 100 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 67 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 100 214 2 33 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 100 214 (accept_3_3 65 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 100 214 2 32 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 100 214 (Polychromatic418967fa.accept_22_19_12_16_1_6241 63 100 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 100 214 2 31 50 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 100 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 61 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 100 214 2 30 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 100 214 (accept_3_3 59 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 100 214 2 29 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 100 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 100 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 100 214 2 28 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 100 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 100 214 2 27 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 100 214 (accept_3_3 53 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 100 214 2 26 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 100 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 100 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 214 2 25 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 100 214 2 24 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 100 214 (accept_3_3 47 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 100 214 2 23 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 100 214 (Polychromatic418967fa.accept_16_13_4_6_1_2322 45 100 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 100 214 2 22 50 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 100 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 100 214 2 21 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 100 214 (accept_3_3 41 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 100 214 2 20 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 100 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 100 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 100 214 2 19 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 100 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 100 214 2 18 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 100 214 (accept_3_3 35 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 100 214 2 17 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 100 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 100 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 100 214 2 16 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 100 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 100 214 2 15 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 100 214 (accept_3_3 29 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 100 214 2 14 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 100 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 100 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 214 2 13 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 100 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 100 214 2 12 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 100 214 (accept_3_3 23 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 100 214 2 11 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 100 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 100 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 100 214 2 10 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 100 214 2 9 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 100 214 (accept_3_3 17 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 100 214 2 8 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 100 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 100 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 100 214 2 7 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 100 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 100 214 2 6 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 100 214 (accept_3_3 11 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 100 214 2 5 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 100 214 (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 100 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 100 214 2 4 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 100 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 100 214 2 3 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 100 214 (accept_3_3 5 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100
  214 2 2 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  100 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 100 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 100 214 2 1 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 100 214 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 100 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 99
  214 (allA_succ_of_accept 98 99 214 (accept_3_3 98 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 99 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 99 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 96 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 214 (accept_3_3 95 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 94 99 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 99 214 (accept_3_3 92 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  99 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 99 214 (Polychromatic418967fa.accept_12_6_3_10_1_224 90 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 99 214 (accept_3_3 89 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 214 (Polychromatic418967fa.accept_10_8_9_4_1_961 88 99 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 87 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 99 214 (accept_3_3 86 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  99 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 99 214 (Polychromatic418967fa.accept_16_4_3_6_1_6805 84 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 99 214 (accept_3_3 83 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 82 99 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 99 214 (accept_3_3 80 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  99 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 99 214 (Polychromatic418967fa.accept_10_8_9_4_1_961 78 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 214 (accept_3_3 77 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 214 (Polychromatic418967fa.accept_13_11_8_6_1_1023 76 99 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 75 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 99 214 (accept_3_3 74 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  99 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 99 214 (Polychromatic418967fa.accept_15_12_9_4_1_3898 72 99 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 214 (accept_3_3 71 99 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 214 (Polychromatic418967fa.accept_15_10_9_4_1_2924 70 99
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 99 214 (accept_3_3 68 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  99 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 99 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 214 (accept_3_3 65 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 214 (Polychromatic418967fa.accept_17_13_14_10_1_1847 64 99 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 214
  (Polychromatic418967fa.accept_10_3_9_4_1_960 63 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 99 214 (accept_3_3 62 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  99 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 214 (Polychromatic418967fa.accept_25_10_24_14_1_12631 60 99 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 214 (accept_3_3 59 99 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 214 (Polychromatic418967fa.accept_10_8_9_4_1_961 58 99 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 99 214 (accept_3_3 56 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  99 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 99 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 214 (accept_3_3 53 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 99 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 214
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 51 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 99 214 (accept_3_3 50 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  99 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 214 (Polychromatic418967fa.accept_10_8_9_4_1_961 48 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 214 (accept_3_3 47 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 214 (Polychromatic418967fa.accept_19_8_4_5_1_8569 46 99 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 99 214 (accept_3_3 44 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  99 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 99 214 (Polychromatic418967fa.accept_12_6_3_10_1_224 42 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 214 (accept_3_3 41 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 99 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 214
  (Polychromatic418967fa.accept_14_11_1_4_1_4445 39 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 214 (accept_3_3 38 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 214 (Polychromatic418967fa.accept_15_6_9_4_1_1227 36 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 214 (accept_3_3 35 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 214 (Polychromatic418967fa.accept_16_2_3_6_1_3372 34 99 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 214 (accept_3_3 32 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 214 (Polychromatic418967fa.accept_12_6_3_10_1_224 30 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 214 (accept_3_3 29 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 214 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 99 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 214
  (Polychromatic418967fa.accept_13_1_8_6_1_1016 27 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 214 (accept_3_3 26 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 214 (accept_3_3 23 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 214 (Polychromatic418967fa.accept_17_5_14_10_1_2831 22 99 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 214 (accept_3_3 20 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 214 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 214 (accept_3_3 17 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 214 (Polychromatic418967fa.accept_25_16_24_14_1_12630 16 99 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 214
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 214 (accept_3_3 14 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 214 (accept_3_3 11 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 99 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 214 (accept_3_3 8 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  214 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 99 214 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 99 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 214 (accept_3_3 5 99 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 99 214 (Polychromatic418967fa.accept_16_4_3_6_1_6805 4 99 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  99 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 214 (accept_3_3 2 99 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 99
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  214 (allA_of_3_1 98 98 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 97 214 (allA_succ_of_accept 96 97 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 96 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 97 214 (accept_3_3 95 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  97 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 94 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 97 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 214 (accept_3_3 92 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 97 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 214
  (Polychromatic418967fa.accept_17_5_12_10_1_3963 90 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 97 214 (accept_3_3 89 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  97 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 88 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 97 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 214 (accept_3_3 86 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 214 (Polychromatic418967fa.accept_15_10_7_4_1_1222 85 97 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 214
  (Polychromatic418967fa.accept_11_7_9_5_1_338 84 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 214 (accept_3_3 83 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 82 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 214 (accept_3_3 80 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 97 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 214
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 78 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 214 (accept_3_3 77 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 76 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 214 (accept_3_3 74 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 97 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 214 (accept_3_3 71 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 214 (Polychromatic418967fa.accept_15_10_7_4_1_1222 70 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 214 (accept_3_3 68 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 97 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 66 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 214 (accept_3_3 65 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 64 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 214 (accept_3_3 62 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 97 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 214
  (Polychromatic418967fa.accept_19_3_2_5_1_5679 60 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 214 (accept_3_3 59 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 214 (accept_3_3 56 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 97 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 214 (accept_3_3 53 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 214 (accept_3_3 50 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 214 (Polychromatic418967fa.accept_21_7_13_4_1_2169 49 97 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 214
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 48 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 214 (accept_3_3 47 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 214 (Polychromatic418967fa.accept_19_8_2_5_1_5678 46 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 214 (accept_3_3 44 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 97 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 214
  (Polychromatic418967fa.accept_10_2_7_4_1_967 42 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 214 (accept_3_3 41 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 214 (accept_3_3 38 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 97 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 214
  (Polychromatic418967fa.accept_17_2_12_10_1_9034 36 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 214 (accept_3_3 35 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 214 (Polychromatic418967fa.accept_16_2_1_6_1_2342 34 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 214 (accept_3_3 32 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 97 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 214 (accept_3_3 29 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 214 (accept_3_3 26 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 214 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 97 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 214 (accept_3_3 23 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 214 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 214 (accept_3_3 20 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 97 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 214
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 214 (accept_3_3 17 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 214 (accept_3_3 14 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 214 (Polychromatic418967fa.accept_10_3_7_4_1_584 13 97 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 214 (accept_3_3 11 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 214 (accept_3_3 8 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 97 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 214
  (Polychromatic418967fa.accept_17_6_12_10_1_7781 6 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 214 (accept_3_3 5 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  214 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 97 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 97 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 214 (accept_3_3 2 97 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 214 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 97 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 214
  (allA_succ_of_accept 95 96 214 (accept_3_3 95 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 96
  214 2 47 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  93 96 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 93 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 96 214 2 46 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 96 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 91 96 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 214 2 45 48 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 214 (accept_3_3 89 96 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 214 2 44 48 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 214
  (Polychromatic418967fa.accept_18_15_6_16_1_4730 87 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 96 214 2 43 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 96 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 85 96 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 214 2 42 48 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 214 (accept_3_3 83 96 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 214 2 41 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 214 (Polychromatic418967fa.accept_13_3_5_6_1_3192
  81 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 96 214 2 40 48 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 79 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 96 214 2 39 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 96 214 (accept_3_3 77 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 96 214 2 38 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 96 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 96 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 96 214 2 37 48 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 96 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 73 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 96 214 2 36 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 96 214 (accept_3_3 71 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 96 214 2 35 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 96 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 96 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 96 214 2 34 48 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 96 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 67 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 96 214 2 33 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 96 214 (accept_3_3 65 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 96 214 2 32 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 96 214 (Polychromatic418967fa.accept_13_11_5_6_1_519 63 96 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 214 2 31 48 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 214
  (Polychromatic418967fa.accept_19_4_1_5_1_9933 61 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 214 2 30 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 96 214 (accept_3_3 59 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 96 214 2 29 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 96 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 96 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 96 214 2 28 48 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 55 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 96 214 2 27 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 96 214 (accept_3_3 53 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 96 214 2 26 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 96 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 96 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 96 214 2 25 48 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 214 2 24 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 96 214 (accept_3_3 47 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 96 214 2 23 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 96 214 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 96 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 96 214 2 22 48 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 214
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 214 2 21 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 96 214 (accept_3_3 41 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 96 214 2 20 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 96 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 96 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 214 2 19 48 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 96 214 2 18 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 96 214 (accept_3_3 35 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 96 214 2 17 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 96 214 (Polychromatic418967fa.accept_18_15_6_16_1_4730 33 96 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 96 214 2 16 48 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 96 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 214 2 15 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 96 214 (accept_3_3 29 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 96 214 2 14 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 96 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 96 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 214 2 13 48 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 214
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 214 2 12 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 96 214 (accept_3_3 23 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 96 214 2 11 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 96 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 96 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 96 214 2 10 48 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 96 214 2 9 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 96 214 (accept_3_3 17 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96
  214 2 8 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  96 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 96 214 2 7 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 96 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 96 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 214 2 6 48 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 214 (accept_3_3 11 96 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 214 2 5 48 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 96 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 96 214 2 4 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 214 (Polychromatic418967fa.accept_21_7_12_4_1_6493 7 96 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 214 2 3 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 214 (accept_3_3 5 96 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 96 214 2 2 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 96 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 96 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 214 2 1 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 96
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 214
  (allA_of_3_1 95 95 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 94 214 (allA_succ_of_accept 93 94 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 93 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 94 214 2 46 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 94 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 94 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 94 214 2 45 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 94 214 (accept_3_3 89 94 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 94 214 2 44 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 94 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 87
  94 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 94 214 2 43 47 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 94 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 85 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 94 214 2 42 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 94 214 (accept_3_3 83 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 94 214 2 41 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 94 214 (Polychromatic418967fa.accept_17_13_9_10_1_2888 81 94 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 94 214 2 40 47 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 94 214
  (Polychromatic418967fa.accept_13_1_3_6_1_158 79 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 94 214 2 39 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 94 214 (accept_3_3 77 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 94 214 2 38 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 94 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 75 94 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 94 214 2 37 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 94 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 73 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 94 214 2 36 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 94 214 (accept_3_3 71 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 94 214 2 35 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 94 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 94 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 94 214 2 34 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 94 214
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 67 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 94 214 2 33 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 94 214 (accept_3_3 65 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 94 214 2 32 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 94 214 (Polychromatic418967fa.accept_14_7_10_4_1_130 63 94 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 94 214 2 31 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 94 214
  (Polychromatic418967fa.accept_13_9_3_6_1_1661 61 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 94 214 2 30 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 94 214 (accept_3_3 59 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 94 214 2 29 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 94 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 94 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 94 214 2 28 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 94 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 55 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 94 214 2 27 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 94 214 (accept_3_3 53 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 94 214 2 26 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 94 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 94 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 94 214 2 25 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 94 214
  (Polychromatic418967fa.accept_13_10_3_6_1_1003 49 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 94 214 2 24 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 94 214 (accept_3_3 47 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 94 214 2 23 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 94 214 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 94 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 94 214 2 22 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 94 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 94 214 2 21 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 94 214 (accept_3_3 41 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 94 214 2 20 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 94 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 94 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 94 214 2 19 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 94 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 94 214 2 18 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 94 214 (accept_3_3 35 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 94 214 2 17 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 94 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 94 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 94 214 2 16 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 94 214
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 31 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 94 214 2 15 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 94 214 (accept_3_3 29 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 94 214 2 14 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 94 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 94 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 94 214 2 13 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 94 214
  (Polychromatic418967fa.accept_18_7_4_16_1_2299 25 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 94 214 2 12 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 94 214 (accept_3_3 23 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 94 214 2 11 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 94 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 94 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 94 214 2 10 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 94 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 94 214 2 9 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 94 214 (accept_3_3 17 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94
  214 2 8 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  94 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 94 214 2 7 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 94 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 94 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 214 2 6 47 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 214 (accept_3_3 11 94 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 214 2 5 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 214
  (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 94 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 94 214 2 4 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 214 (Polychromatic418967fa.accept_14_7_10_4_1_130 7 94 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 214 2 3 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 214 (accept_3_3 5 94 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 214 2 2 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 94 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 214 2 1 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 94
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 214
  (allA_succ_of_accept 92 93 214 (accept_3_3 92 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  93 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 93 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 90 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 214 (accept_3_3 89 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 214 (Polychromatic418967fa.accept_13_10_2_6_1_1044 88 93 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 214 (accept_3_3 86 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 214 (Polychromatic418967fa.accept_16_4_13_6_1_4417 84 93 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 214 (accept_3_3 83 93 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 82 93 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 214
  (Polychromatic418967fa.accept_20_1_13_14_1_1481 81 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 214 (accept_3_3 80 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 78 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 214 (accept_3_3 77 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 93 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 214 (accept_3_3 74 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 214 (Polychromatic418967fa.accept_14_2_9_4_1_1735 72 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 214 (accept_3_3 71 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 214 (Polychromatic418967fa.accept_17_2_8_10_1_2870 70 93 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 214 (accept_3_3 68 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 214 (Polychromatic418967fa.accept_12_6_9_10_1_565 66 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 214 (accept_3_3 65 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 93 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 214 (accept_3_3 62 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 60 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 214 (accept_3_3 59 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 93 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 214
  (Polychromatic418967fa.accept_10_7_3_4_1_978 57 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 214 (accept_3_3 56 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 214 (accept_3_3 53 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 214 (Polychromatic418967fa.accept_15_7_3_4_1_574 52 93 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 214 (accept_3_3 50 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 214 (accept_3_3 47 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 93 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 214
  (Polychromatic418967fa.accept_19_7_17_5_1_3081 45 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 214 (accept_3_3 44 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 214 (accept_3_3 41 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 93 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 214 (accept_3_3 38 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 214 (Polychromatic418967fa.accept_13_10_2_6_1_1044 36 93 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 214 (accept_3_3 35 93 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 93 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 214 (accept_3_3 32 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 214 (Polychromatic418967fa.accept_12_6_9_10_1_565 30 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 214 (accept_3_3 29 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 93 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 214 (accept_3_3 26 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 214 (accept_3_3 23 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 93 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 214
  (Polychromatic418967fa.accept_13_8_2_6_1_2385 21 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 214 (accept_3_3 20 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 214 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 214 (accept_3_3 17 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 214 (Polychromatic418967fa.accept_14_2_9_4_1_1735 16 93 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 214 (accept_3_3 14 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 214 (accept_3_3 11 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 93 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 214
  (Polychromatic418967fa.accept_10_9_3_4_1_985 9 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 214 (accept_3_3 8 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 93 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 93 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 214 (accept_3_3 5 93 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 93 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 214 (accept_3_3 2 93 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 214
  (allA_of_3_1 92 92 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 214 (allA_succ_of_accept 90 91 214
  (Polychromatic418967fa.accept_20_10_11_14_1_8380 90 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 91 214 (accept_3_3 89 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 91 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 88 91 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 91 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 214 (accept_3_3 86 91 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 85
  91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 91 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 84 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 91 214 (accept_3_3 83 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  91 214 (Polychromatic418967fa.accept_16_2_11_6_1_737 82 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 91 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 214 (accept_3_3 80 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 214 (Polychromatic418967fa.accept_18_7_1_16_1_578 79 91 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 91 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 78 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 91 214 (accept_3_3 77 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  91 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 91 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 214 (accept_3_3 74 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 91 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 214
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 72 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 91 214 (accept_3_3 71 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  91 214 (Polychromatic418967fa.accept_20_10_11_14_1_8380 70 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 91 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 214 (accept_3_3 68 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 91 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 91 214 (accept_3_3 65 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  91 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 64 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 91 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 214 (accept_3_3 62 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 91 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 91 214 (accept_3_3 59 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  91 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 91 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 214 (accept_3_3 56 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 214 (Polychromatic418967fa.accept_10_5_1_4_1_1444 55 91 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 214
  (Polychromatic418967fa.accept_21_12_7_4_1_12629 54 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 214 (accept_3_3 53 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 214 (Polychromatic418967fa.accept_11_8_3_5_1_355 52 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 214 (accept_3_3 50 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 91 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 214 (accept_3_3 47 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 214 (Polychromatic418967fa.accept_17_12_6_10_1_7807 46 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 214 (accept_3_3 44 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 214 (Polychromatic418967fa.accept_18_7_1_16_1_578 43 91 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 214 (accept_3_3 41 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 214 (accept_3_3 38 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 91 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 214
  (Polychromatic418967fa.accept_16_4_11_6_1_5591 36 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 214 (accept_3_3 35 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 214 (Polychromatic418967fa.accept_16_2_11_6_1_737 34 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 214 (accept_3_3 32 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 91 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 214 (accept_3_3 29 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 214 (accept_3_3 26 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 91 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 214 (accept_3_3 23 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 214 (accept_3_3 20 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 214 (Polychromatic418967fa.accept_11_8_3_5_1_355 19 91 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 214
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 214 (accept_3_3 17 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 214 (accept_3_3 14 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 91 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 214 (accept_3_3 11 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 214 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 214 (accept_3_3 8 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 214 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 91 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 214 (accept_3_3 5 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  214 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 91 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 214 (accept_3_3 2 91 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 214
  (allA_succ_of_accept 89 90 214 (accept_3_3 89 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 90
  214 2 44 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  87 90 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 90 214 2 43 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 90 214 (Polychromatic418967fa.accept_11_8_2_5_1_1769 85 90 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 214 2 42 45 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 214 (accept_3_3 83 90 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 214 2 41 45 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 90 214
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 81 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 90 214 2 40 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 90 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 79 90 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 214 2 39 45 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 214 (accept_3_3 77 90 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 214 2 38 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 90 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 75
  90 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 90 214 2 37 45 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 90 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 73 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 214 2 36 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 90 214 (accept_3_3 71 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 90 214 2 35 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 90 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 69 90 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 90 214 2 34 45 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 90 214
  (Polychromatic418967fa.accept_13_2_12_6_1_2394 67 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 214 2 33 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 90 214 (accept_3_3 65 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 90 214 2 32 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 90 214 (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 90 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 90 214 2 31 45 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 90 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 61 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 214 2 30 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 90 214 (accept_3_3 59 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 90 214 2 29 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 90 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 57 90 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 90 214 2 28 45 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 90 214
  (Polychromatic418967fa.accept_19_17_14_5_1_8561 55 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 214 2 27 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 90 214 (accept_3_3 53 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 90 214 2 26 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 90 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 90 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 90 214 2 25 45 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 214
  (Polychromatic418967fa.accept_13_10_12_6_1_991 49 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 214 2 24 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 90 214 (accept_3_3 47 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 90 214 2 23 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 90 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 90 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 90 214 2 22 45 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 214
  (Polychromatic418967fa.accept_27_16_9_25_1_12628 43 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 90 214 2 21 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 90 214 (accept_3_3 41 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 90 214 2 20 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 90 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 90 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 214 2 19 45 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 214 2 18 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 90 214 (accept_3_3 35 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 90 214 2 17 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 90 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 90 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 90 214 2 16 45 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 214 2 15 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 90 214 (accept_3_3 29 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 90 214 2 14 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 90 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 90 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 214 2 13 45 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 214
  (Polychromatic418967fa.accept_19_6_14_5_1_4339 25 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 214 2 12 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 90 214 (accept_3_3 23 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 90 214 2 11 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 90 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 90 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 214 2 10 45 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 214 2 9 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 214 (accept_3_3 17 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90
  214 2 8 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  90 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 90 214 2 7 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 90 214 (Polychromatic418967fa.accept_17_13_5_10_1_2839 13 90 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 214 2 6 45 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 214 (accept_3_3 11 90 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 214 2 5 45 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 90 214 2 4 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 214 (Polychromatic418967fa.accept_13_7_12_6_1_1039 7 90 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 214 2 3 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 214 (accept_3_3 5 90 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 90 214 2 2 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 90 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 90 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 214 2 1 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 214 (Polychromatic418967fa.accept_20_1_10_14_1_1472
  1 90 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 214
  (allA_of_3_1 89 89 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 214 (allA_succ_of_accept 87 88 214
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 87 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 88 214 2 43 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 88 214 (Polychromatic418967fa.accept_12_1_4_10_1_209 85 88 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 88 214 2 42 44 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 88 214 (accept_3_3 83 88 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 88 214 2 41 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 88 214 (Polychromatic418967fa.accept_13_3_10_6_1_2382
  81 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 88 214 2 40 44 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 88 214
  (Polychromatic418967fa.accept_10_9_8_4_1_970 79 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 88 214 2 39 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 88 214 (accept_3_3 77 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 88 214 2 38 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 88 214 (Polychromatic418967fa.accept_17_7_3_10_1_2881 75 88 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 88 214 2 37 44 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 88 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 73 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 88 214 2 36 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 88 214 (accept_3_3 71 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 88 214 2 35 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 88 214 (Polychromatic418967fa.accept_10_9_8_4_1_970 69 88 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 88 214 2 34 44 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 88 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 67 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 88 214 2 33 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 88 214 (accept_3_3 65 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 88 214 2 32 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 88 214 (Polychromatic418967fa.accept_20_3_8_14_1_5342 63 88 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 88 214 2 31 44 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 88 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 88 214 2 30 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 88 214 (accept_3_3 59 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 88 214 2 29 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 88 214 (Polychromatic418967fa.accept_13_5_10_6_1_2361 57 88 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 88 214 2 28 44 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 88 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 55 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 88 214 2 27 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 88 214 (accept_3_3 53 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 88 214 2 26 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 88 214 (Polychromatic418967fa.accept_13_12_10_6_1_3212 51 88 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 88 214 2 25 44 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 88 214
  (Polychromatic418967fa.accept_10_9_8_4_1_970 49 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 88 214 2 24 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 88 214 (accept_3_3 47 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 88 214 2 23 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 88 214 (Polychromatic418967fa.accept_17_11_3_10_1_2838 45 88 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 88 214 2 22 44 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 88 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 88 214 2 21 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 88 214 (accept_3_3 41 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 88 214 2 20 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 88 214 (Polychromatic418967fa.accept_10_9_8_4_1_970 39 88 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 88 214 2 19 44 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 88 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 88 214 2 18 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 88 214 (accept_3_3 35 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 88 214 2 17 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 88 214 (Polychromatic418967fa.accept_20_13_8_14_1_1467 33 88 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 88 214 2 16 44 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 88 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 88 214 2 15 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 88 214 (accept_3_3 29 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 88 214 2 14 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 88 214 (Polychromatic418967fa.accept_19_8_12_5_1_7122 27 88 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 88 214 2 13 44 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 88 214 2 12 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 88 214 (accept_3_3 23 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 88 214 2 11 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 88 214 (Polychromatic418967fa.accept_15_6_13_4_1_2040 21 88 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 88 214 2 10 44 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 88 214
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 88 214 2 9 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 88 214 (accept_3_3 17 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88
  214 2 8 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  88 214 (Polychromatic418967fa.accept_13_2_10_6_1_1676 15 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 88 214 2 7 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 88 214 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 88 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 214 2 6 44 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 88 214 (accept_3_3 11 88 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88 214 2 5 44 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 88 214
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 88 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 88 214 2 4 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 88 214 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 88 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 214 2 3 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 214 (accept_3_3 5 88 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 88 214 2 2 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 88 214 (Polychromatic418967fa.accept_13_3_10_6_1_2382 3 88 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 214 2 1 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 214 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  88 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 214
  (allA_succ_of_accept 86 87 214 (accept_3_3 86 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  87 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 84 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 214 (accept_3_3 83 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 87 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 214 (accept_3_3 80 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 214 (accept_3_3 77 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 87 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 75 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 214 (accept_3_3 74 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 214 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 214 (accept_3_3 71 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 214 (Polychromatic418967fa.accept_11_4_10_5_1_1202 70 87 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 214 (accept_3_3 68 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 214 (accept_3_3 65 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 87 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 214
  (Polychromatic418967fa.accept_10_3_7_4_1_584 63 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 214 (accept_3_3 62 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 214 (Polychromatic418967fa.accept_18_6_15_16_1_7325 60 87 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 214 (accept_3_3 59 87 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 87 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 214 (accept_3_3 56 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 214 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 214 (accept_3_3 53 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 214 (Polychromatic418967fa.accept_10_2_7_4_1_967 52 87 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 214
  (Polychromatic418967fa.accept_10_1_7_4_1_968 51 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 214 (accept_3_3 50 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 214 (accept_3_3 47 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 87 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 214 (accept_3_3 44 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 214 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 214 (accept_3_3 41 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 87 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 214 (accept_3_3 38 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 214 (accept_3_3 35 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 87 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 214 (accept_3_3 32 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 214 (accept_3_3 29 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 87 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 214 (accept_3_3 26 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 214 (Polychromatic418967fa.accept_15_9_12_4_1_2023 24 87 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 214 (accept_3_3 23 87 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 87 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 214 (accept_3_3 20 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 214 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 214 (accept_3_3 17 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 214 (Polychromatic418967fa.accept_13_3_9_6_1_502 16 87 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 214 (accept_3_3 14 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 214 (accept_3_3 11 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 87 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 214 (accept_3_3 8 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  214 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 87 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 214 (accept_3_3 5 87 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 87 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 3
  87 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 214 (accept_3_3 2 87 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 214
  (allA_of_3_1 86 86 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 214 (allA_succ_of_accept 84 85 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 84 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 214 (accept_3_3 83 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 82 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 214 (accept_3_3 80 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 85 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 85 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 78 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 85 214 (accept_3_3 77 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  85 214 (Polychromatic418967fa.accept_10_6_5_4_1_571 76 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 85 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 214 (accept_3_3 74 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 85 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 214
  (Polychromatic418967fa.accept_19_15_9_5_1_5656 72 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 214 (accept_3_3 71 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 214 (Polychromatic418967fa.accept_19_13_9_5_1_8541 70 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 214 (accept_3_3 68 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 85 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 66 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 214 (accept_3_3 65 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 214 (accept_3_3 62 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 85 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 214 (accept_3_3 59 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 214 (Polychromatic418967fa.accept_11_3_8_5_1_336 58 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 214 (accept_3_3 56 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 85 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 214 (accept_3_3 53 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 214 (accept_3_3 50 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 214 (Polychromatic418967fa.accept_10_9_5_4_1_966 49 85 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 214 (accept_3_3 47 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 214 (accept_3_3 44 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 85 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 214 (accept_3_3 41 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 214 (accept_3_3 38 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 85 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 214
  (Polychromatic418967fa.accept_10_6_5_4_1_571 36 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 214 (accept_3_3 35 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 214 (Polychromatic418967fa.accept_19_15_9_5_1_5656 34 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 214 (accept_3_3 32 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 85 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 214 (accept_3_3 29 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 214 (accept_3_3 26 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 214 (Polychromatic418967fa.accept_11_3_8_5_1_336 25 85 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 214 (accept_3_3 23 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 214 (Polychromatic418967fa.accept_13_9_7_6_1_1673 22 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 214 (accept_3_3 20 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 85 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 214
  (Polychromatic418967fa.accept_19_18_9_5_1_8542 18 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 214 (accept_3_3 17 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 214 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 214 (accept_3_3 14 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 214 (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 85 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 214 (accept_3_3 11 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 214 (accept_3_3 8 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 214 (accept_3_3 5 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  214 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 85 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 85 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 214 (accept_3_3 2 85 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 85 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 214
  (allA_succ_of_accept 83 84 214 (accept_3_3 83 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 84
  214 2 41 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  81 84 214 (Polychromatic418967fa.accept_15_6_9_4_1_1227 81 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 84 214 2 40 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 84 214 (Polychromatic418967fa.accept_19_3_8_5_1_1875 79 84 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 214 2 39 42 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 214 (accept_3_3 77 84 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 214 2 38 42 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 214
  (Polychromatic418967fa.accept_11_9_7_5_1_749 75 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 214 2 37 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 84 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 84 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 214 2 36 42 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 214 (accept_3_3 71 84 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 214 2 35 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 69
  84 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 214 2 34 42 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 214 2 33 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 84 214 (accept_3_3 65 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 214 2 32 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 84 214 (Polychromatic418967fa.accept_18_9_12_16_1_7323 63 84 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 214 2 31 42 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 214
  (Polychromatic418967fa.accept_16_13_4_6_1_2322 61 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 84 214 2 30 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 84 214 (accept_3_3 59 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 84 214 2 29 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 84 214 (Polychromatic418967fa.accept_15_12_9_4_1_3898 57 84 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 84 214 2 28 42 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 84 214 2 27 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 84 214 (accept_3_3 53 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 84 214 2 26 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 84 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 84 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 214 2 25 42 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 214 2 24 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 84 214 (accept_3_3 47 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 84 214 2 23 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 84 214 (Polychromatic418967fa.accept_16_13_4_6_1_2322 45 84 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 214 2 22 42 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 214
  (Polychromatic418967fa.accept_15_13_9_4_1_3892 43 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 84 214 2 21 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 84 214 (accept_3_3 41 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 84 214 2 20 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 84 214 (Polychromatic418967fa.accept_20_19_4_14_1_8345 39 84 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 84 214 2 19 42 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 214 2 18 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 84 214 (accept_3_3 35 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 84 214 2 17 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 84 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 84 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 214 2 16 42 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 214 2 15 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 84 214 (accept_3_3 29 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 214 2 14 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 84 214 (Polychromatic418967fa.accept_15_12_9_4_1_3898 27 84 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 214 2 13 42 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 214
  (Polychromatic418967fa.accept_15_10_9_4_1_2924 25 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 214 2 12 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 84 214 (accept_3_3 23 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 84 214 2 11 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 84 214 (Polychromatic418967fa.accept_15_6_9_4_1_1227 21 84 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 84 214 2 10 42 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 214 2 9 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 214 (accept_3_3 17 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84
  214 2 8 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  84 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 84 214 2 7 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 84 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 84 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 214 2 6 42 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 214 (accept_3_3 11 84 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 214 2 5 42 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 214
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 84 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 214 2 4 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 214 (Polychromatic418967fa.accept_17_7_16_10_1_1849 7 84 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 214 2 3 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 214 (accept_3_3 5 84 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 84 214 2 2 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 84 214 (Polychromatic418967fa.accept_16_3_4_6_1_6798 3 84 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 214 2 1 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 84
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 214 (allA_of_3_1
  83 83 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 214 (allA_succ_of_accept 81 82 214
  (Polychromatic418967fa.accept_16_1_2_6_1_2295 81 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 82 214 2 40 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 82 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 79 82 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 82 214 2 39 41 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 82 214 (accept_3_3 77 82 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 82 214 2 38 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 82 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 75
  82 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 82 214 2 37 41 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 82 214
  (Polychromatic418967fa.accept_16_9_2_6_1_4434 73 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 82 214 2 36 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 82 214 (accept_3_3 71 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 82 214 2 35 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 82 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 82 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 82 214 2 34 41 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 82 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 67 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 82 214 2 33 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 82 214 (accept_3_3 65 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 82 214 2 32 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 82 214 (Polychromatic418967fa.accept_13_11_4_6_1_1006 63 82 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 82 214 2 31 41 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 82 214
  (Polychromatic418967fa.accept_13_9_4_6_1_1005 61 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 82 214 2 30 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 82 214 (accept_3_3 59 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 82 214 2 29 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 82 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 82 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 82 214 2 28 41 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 82 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 55 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 82 214 2 27 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 82 214 (accept_3_3 53 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 82 214 2 26 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 82 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 82 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 82 214 2 25 41 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 82 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 82 214 2 24 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 82 214 (accept_3_3 47 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 82 214 2 23 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 82 214 (Polychromatic418967fa.accept_19_7_6_5_1_4320 45 82 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 82 214 2 22 41 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 82 214
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 82 214 2 21 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 82 214 (accept_3_3 41 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 82 214 2 20 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 82 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 82 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 82 214 2 19 41 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 82 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 82 214 2 18 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 82 214 (accept_3_3 35 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 82 214 2 17 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 82 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 82 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 82 214 2 16 41 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 82 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 82 214 2 15 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 82 214 (accept_3_3 29 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 82 214 2 14 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 82 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 82 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 82 214 2 13 41 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 82 214
  (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 82 214 2 12 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 82 214 (accept_3_3 23 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 82 214 2 11 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 82 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 82 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 82 214 2 10 41 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 82 214
  (Polychromatic418967fa.accept_16_3_2_6_1_4461 19 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 82 214 2 9 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 82 214 (accept_3_3 17 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82
  214 2 8 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  82 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 82 214 2 7 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 82 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 82 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 214 2 6 41 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 214 (accept_3_3 11 82 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 214 2 5 41 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 82 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 214 2 4 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 82 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 214 2 3 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 214 (accept_3_3 5 82 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 214 2 2 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 82 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 214 2 1 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 82
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 214
  (allA_succ_of_accept 80 81 214 (accept_3_3 80 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 214 (Polychromatic418967fa.accept_12_6_9_10_1_565 78 81 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 214 (accept_3_3 77 81 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 214 (Polychromatic418967fa.accept_11_10_4_5_1_359 76 81 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 214 (accept_3_3 74 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 214 (Polychromatic418967fa.accept_21_9_18_4_1_4953 72 81 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 214 (accept_3_3 71 81 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 214 (Polychromatic418967fa.accept_13_5_3_6_1_3278 70 81 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 214
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 69 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 214 (accept_3_3 68 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 214 (Polychromatic418967fa.accept_12_6_9_10_1_565 66 81 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 214 (accept_3_3 65 81 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 214 (Polychromatic418967fa.accept_14_8_11_4_1_3438 64 81 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 214 (accept_3_3 62 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 214 (Polychromatic418967fa.accept_17_9_13_10_1_1825 60 81 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 214 (accept_3_3 59 81 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 214 (Polychromatic418967fa.accept_15_13_6_4_1_1221 58 81
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 214
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 57 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 214 (accept_3_3 56 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 214 (Polychromatic418967fa.accept_11_10_4_5_1_359 54 81 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 214 (accept_3_3 53 81 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 214 (Polychromatic418967fa.accept_37_15_7_29_1_12627 52 81 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 214 (accept_3_3 50 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 214 (Polychromatic418967fa.accept_13_9_3_6_1_1661 48 81 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 214 (accept_3_3 47 81 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 214 (Polychromatic418967fa.accept_20_6_1_14_1_11258 46 81 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 214
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 214 (accept_3_3 44 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 214 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 81 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 214 (accept_3_3 41 81 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 214 (Polychromatic418967fa.accept_13_1_3_6_1_158 40 81 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 214 (accept_3_3 38 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 214 (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 81 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 214 (accept_3_3 35 81 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 214 (Polychromatic418967fa.accept_16_2_1_6_1_2342 34 81 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 214
  (Polychromatic418967fa.accept_18_15_9_16_1_6029 33 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 214 (accept_3_3 32 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 214 (Polychromatic418967fa.accept_12_6_9_10_1_565 30 81 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 214 (accept_3_3 29 81 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 214 (Polychromatic418967fa.accept_15_13_6_4_1_1221 28 81 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 214 (accept_3_3 26 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 214 (Polychromatic418967fa.accept_15_9_6_4_1_1220 24 81 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 214 (accept_3_3 23 81 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 214 (Polychromatic418967fa.accept_13_9_3_6_1_1661 22 81 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 214
  (Polychromatic418967fa.accept_11_10_4_5_1_359 21 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 214 (accept_3_3 20 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 214 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 81 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 214 (accept_3_3 17 81 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 214 (Polychromatic418967fa.accept_23_16_12_7_1_12626 16 81 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 214 (accept_3_3 14 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 214 (Polychromatic418967fa.accept_18_12_9_16_1_4732 12 81 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 214 (accept_3_3 11 81 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 214 (Polychromatic418967fa.accept_11_10_4_5_1_359 10 81 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 214
  (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 214 (accept_3_3 8 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 214 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 81 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 214 (accept_3_3 5 81 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 214 (Polychromatic418967fa.accept_22_4_15_16_1_6184 4 81 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 214 (accept_3_3 2 81 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 214 (allA_of_3_1 80
  80 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 214 (allA_succ_of_accept 78 79 214
  (Polychromatic418967fa.accept_10_8_9_4_1_961 78 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 79 214 (accept_3_3 77 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  79 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 79 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 214 (accept_3_3 74 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 79 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 214
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 72 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 214 (accept_3_3 71 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 214 (Polychromatic418967fa.accept_13_5_1_6_1_2367 70 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 214 (accept_3_3 68 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 214 (Polychromatic418967fa.accept_13_2_1_6_1_2365 67 79 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 214
  (Polychromatic418967fa.accept_20_6_19_14_1_8387 66 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 214 (accept_3_3 65 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 64 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 214 (accept_3_3 62 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 79 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 214
  (Polychromatic418967fa.accept_13_8_1_6_1_997 60 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 214 (accept_3_3 59 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 214 (Polychromatic418967fa.accept_10_8_9_4_1_961 58 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 214 (accept_3_3 56 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 79 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 214 (accept_3_3 53 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 214 (Polychromatic418967fa.accept_11_8_2_5_1_1769 52 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 214 (accept_3_3 50 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 79 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 214 (accept_3_3 47 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 214 (Polychromatic418967fa.accept_13_7_1_6_1_3287 46 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 214 (accept_3_3 44 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 214 (Polychromatic418967fa.accept_10_3_9_4_1_960 43 79 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 214
  (Polychromatic418967fa.accept_13_3_1_6_1_509 42 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 214 (accept_3_3 41 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 214 (accept_3_3 38 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 79 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 214
  (Polychromatic418967fa.accept_19_17_3_5_1_3088 36 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 214 (accept_3_3 35 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 214 (accept_3_3 32 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 214 (Polychromatic418967fa.accept_13_5_1_6_1_2367 31 79 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 214
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 214 (accept_3_3 29 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 214 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 214 (accept_3_3 26 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 79 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 214
  (Polychromatic418967fa.accept_20_4_19_14_1_5327 24 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 214 (accept_3_3 23 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 214 (Polychromatic418967fa.accept_13_9_1_6_1_510 22 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 214 (accept_3_3 20 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 79 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 214
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 214 (accept_3_3 17 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 214 (accept_3_3 14 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 214 (accept_3_3 11 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 214 (Polychromatic418967fa.accept_19_10_3_5_1_11346 10 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 214 (accept_3_3 8 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 214 (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 79 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 214 (accept_3_3 5 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  214 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 79 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 79 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 214 (accept_3_3 2 79 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 214
  (allA_succ_of_accept 77 78 214 (accept_3_3 77 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78
  214 2 38 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  75 78 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 78 214 2 37 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 78 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 78 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 214 2 36 39 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 214 (accept_3_3 71 78 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 214 2 35 39 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 78 214
  (Polychromatic418967fa.accept_10_9_8_4_1_970 69 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 78 214 2 34 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 78 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 78 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 214 2 33 39 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 214 (accept_3_3 65 78 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 214 2 32 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 214 (Polychromatic418967fa.accept_12_3_6_10_1_576
  63 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 78 214 2 31 39 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 214 2 30 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 78 214 (accept_3_3 59 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 78 214 2 29 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 78 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 78 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 78 214 2 28 39 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 214 2 27 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 78 214 (accept_3_3 53 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 78 214 2 26 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 78 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 78 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 214 2 25 39 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 214 2 24 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 78 214 (accept_3_3 47 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 78 214 2 23 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 78 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 78 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 78 214 2 22 39 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 214
  (Polychromatic418967fa.accept_25_18_3_14_1_12625 43 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 78 214 2 21 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 78 214 (accept_3_3 41 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 78 214 2 20 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 78 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 78 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 78 214 2 19 39 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 214 2 18 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 78 214 (accept_3_3 35 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 78 214 2 17 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 78 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 78 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 214 2 16 39 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 214 2 15 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 78 214 (accept_3_3 29 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 78 214 2 14 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 78 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 78 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 214 2 13 39 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 214
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 25 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 214 2 12 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 78 214 (accept_3_3 23 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 78 214 2 11 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 78 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 78 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 214 2 10 39 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 214 2 9 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 214 (accept_3_3 17 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78
  214 2 8 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  78 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 78 214 2 7 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 78 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 78 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 214 2 6 39 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 214 (accept_3_3 11 78 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 214 2 5 39 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 214
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 78 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 78 214 2 4 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 214 (Polychromatic418967fa.accept_15_7_3_4_1_574 7 78 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 214 2 3 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 214 (accept_3_3 5 78 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 78 214 2 2 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 78 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 78 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 214 2 1 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 78
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 214 (allA_of_3_1 77 77
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 214 (allA_succ_of_accept 75 76 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 75 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 76 214 2 37 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 76 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 76 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 76 214 2 36 38 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 76 214 (accept_3_3 71 76 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76 214 2 35 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 76 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 69
  76 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 76 214 2 34 38 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 76 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 67 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 76 214 2 33 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 76 214 (accept_3_3 65 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 76 214 2 32 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 76 214 (Polychromatic418967fa.accept_15_3_1_4_1_1246 63 76 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 76 214 2 31 38 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 76 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 61 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 76 214 2 30 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 76 214 (accept_3_3 59 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 76 214 2 29 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 76 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 76 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 76 214 2 28 38 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 76 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 76 214 2 27 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 76 214 (accept_3_3 53 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 76 214 2 26 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 76 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 76 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 214 2 25 38 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 214 2 24 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 76 214 (accept_3_3 47 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 76 214 2 23 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 76 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 76 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 76 214 2 22 38 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 76 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 76 214 2 21 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 76 214 (accept_3_3 41 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 76 214 2 20 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 76 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 76 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 76 214 2 19 38 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 76 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 76 214 2 18 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 76 214 (accept_3_3 35 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 76 214 2 17 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 76 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 76 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 214 2 16 38 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 214 2 15 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 76 214 (accept_3_3 29 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 76 214 2 14 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 76 214 (Polychromatic418967fa.accept_15_12_1_4_1_2899 27 76 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 76 214 2 13 38 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 76 214
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 76 214 2 12 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 76 214 (accept_3_3 23 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 76 214 2 11 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 76 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 76 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 214 2 10 38 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 76 214 2 9 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 76 214 (accept_3_3 17 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76
  214 2 8 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  76 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 76 214 2 7 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 76 214 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 76 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 214 2 6 38 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 214 (accept_3_3 11 76 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 214 2 5 38 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 76 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 76 214 2 4 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 76 214 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 76 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 214 2 3 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 214 (accept_3_3 5 76 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 76 214 2 2 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 76 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 76 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 214 2 1 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 76
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 214 (allA_succ_of_accept
  74 75 214 (accept_3_3 74 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 73 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 75 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 214 (accept_3_3 71 75 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 75 214 (Polychromatic418967fa.accept_13_5_10_6_1_2361 70 75 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 75 214 (accept_3_3 68 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  75 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 75 214 (Polychromatic418967fa.accept_10_6_5_4_1_571 66 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 214 (accept_3_3 65 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 75 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 214
  (Polychromatic418967fa.accept_19_6_18_5_1_5630 63 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 75 214 (accept_3_3 62 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  75 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 75 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 60 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 214 (accept_3_3 59 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 75 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 75 214 (accept_3_3 56 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  75 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 75 214 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 214 (accept_3_3 53 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 214 (Polychromatic418967fa.accept_16_4_11_6_1_5591 52 75 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 75 214 (accept_3_3 50 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  75 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 75 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 214 (accept_3_3 47 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 75 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 75 214 (accept_3_3 44 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  75 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 75 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 214 (accept_3_3 41 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 75 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 214
  (Polychromatic418967fa.accept_10_9_5_4_1_966 39 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 214 (accept_3_3 38 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  75 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 214 (accept_3_3 35 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 75 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 75 214 (accept_3_3 32 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  75 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 75 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 214 (accept_3_3 29 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 75 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 75 214 (accept_3_3 26 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  75 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 75 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 214 (accept_3_3 23 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 75 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 75 214 (accept_3_3 20 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  75 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 75 214 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 214 (accept_3_3 17 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 75 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 214
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 214 (accept_3_3 14 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  75 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 214 (Polychromatic418967fa.accept_13_12_10_6_1_3212 12 75 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 214 (accept_3_3 11 75 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 75 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 214 (accept_3_3 8 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75
  214 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 75 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 75 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 214 (accept_3_3 5 75 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 75 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 75 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 214 (Polychromatic418967fa.accept_13_3_10_6_1_2382
  3 75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 214 (accept_3_3 2 75
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1
  75 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 214 (allA_of_3_1 74 74
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 214 (allA_succ_of_accept 72 73 214
  (Polychromatic418967fa.accept_23_3_4_7_1_12624 72 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 214 (accept_3_3 71 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 214 (Polychromatic418967fa.accept_15_10_13_4_1_1210 70 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 214 (accept_3_3 68 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 73 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 214 (accept_3_3 65 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 214 (accept_3_3 62 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 214 (Polychromatic418967fa.accept_16_13_9_6_1_2306 61 73 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 214 (accept_3_3 59 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 214 (accept_3_3 56 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 73 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 214
  (Polychromatic418967fa.accept_13_2_8_6_1_2390 54 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 214 (accept_3_3 53 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 214 (accept_3_3 50 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 73 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 214 (accept_3_3 47 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 214 (Polychromatic418967fa.accept_17_12_5_10_1_5160 46 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 214 (accept_3_3 44 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 73 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 214 (accept_3_3 41 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 214 (accept_3_3 38 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 214 (Polychromatic418967fa.accept_10_7_3_4_1_978 37 73 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 214 (accept_3_3 35 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 214 (accept_3_3 32 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 73 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 214 (accept_3_3 29 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 214 (accept_3_3 26 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 214 (Polychromatic418967fa.accept_15_10_13_4_1_1210 25 73 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 214 (accept_3_3 23 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 214 (accept_3_3 20 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 214
  (Polychromatic418967fa.accept_16_2_9_6_1_4441 18 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 214 (accept_3_3 17 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 214 (accept_3_3 14 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 73 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 214 (accept_3_3 11 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 214 (Polychromatic418967fa.accept_15_10_13_4_1_1210 10 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 214 (accept_3_3 8 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 214 (accept_3_3 5 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  214 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 73 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 214 (accept_3_3 2 73 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 73 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 214 (allA_succ_of_accept 71
  72 214 (accept_3_3 71 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 72 214 2 35 36 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 72 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 72 214 2 34 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 72 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 67 72 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 214 2 33 36 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 214 (accept_3_3 65 72 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 214 2 32 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 214 (Polychromatic418967fa.accept_19_6_15_5_1_5697
  63 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 214 2 31 36 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 61 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 214 2 30 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 72 214 (accept_3_3 59 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 72 214 2 29 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 72 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 57 72 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 214 2 28 36 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 214 2 27 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 72 214 (accept_3_3 53 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 72 214 2 26 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 72 214 (Polychromatic418967fa.accept_13_12_7_6_1_1015 51 72 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 214 2 25 36 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 214
  (Polychromatic418967fa.accept_17_15_4_10_1_3968 49 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 72 214 2 24 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 72 214 (accept_3_3 47 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 72 214 2 23 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 72 214 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 72 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 214 2 22 36 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 214
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 43 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 214 2 21 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 72 214 (accept_3_3 41 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 72 214 2 20 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 72 214 (Polychromatic418967fa.accept_15_9_12_4_1_2023 39 72 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 214 2 19 36 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 214
  (Polychromatic418967fa.accept_10_7_2_4_1_569 37 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 214 2 18 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 72 214 (accept_3_3 35 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 72 214 2 17 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 72 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 72 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 72 214 2 16 36 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 214
  (Polychromatic418967fa.accept_15_1_12_4_1_2022 31 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 72 214 2 15 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 72 214 (accept_3_3 29 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 72 214 2 14 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 72 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 72 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 214 2 13 36 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 214
  (Polychromatic418967fa.accept_13_12_7_6_1_1015 25 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 214 2 12 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 72 214 (accept_3_3 23 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 72 214 2 11 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 72 214 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 72 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 72 214 2 10 36 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 214 2 9 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 214 (accept_3_3 17 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72
  214 2 8 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  72 214 (Polychromatic418967fa.accept_17_15_4_10_1_3968 15 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 72 214 2 7 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 72 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 72 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 214 2 6 36 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 214 (accept_3_3 11 72 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 214 2 5 36 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 214
  (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 72 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 214 2 4 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 72 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 214 2 3 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 214 (accept_3_3 5 72 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 72 214 2 2 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 72 214 (Polychromatic418967fa.accept_28_3_16_18_1_12623 3 72 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 214 2 1 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 214 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1
  72 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 214 (allA_of_3_1 71 71 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 214 (allA_succ_of_accept 69 70 214
  (Polychromatic418967fa.accept_13_4_5_6_1_3201 69 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 70 214 2 34 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 70 214 (Polychromatic418967fa.accept_15_7_10_4_1_151 67 70 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 214 2 33 35 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 70 214 (accept_3_3 65 70 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 70 214 2 32 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 70 214 (Polychromatic418967fa.accept_13_11_5_6_1_519
  63 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 70 214 2 31 35 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 70 214
  (Polychromatic418967fa.accept_20_1_10_14_1_1472 61 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 70 214 2 30 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 70 214 (accept_3_3 59 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 70 214 2 29 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 70 214 (Polychromatic418967fa.accept_25_7_20_14_1_10958 57 70 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 70 214 2 28 35 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 70 214
  (Polychromatic418967fa.accept_13_3_5_6_1_3192 55 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 70 214 2 27 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 70 214 (accept_3_3 53 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 70 214 2 26 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 70 214 (Polychromatic418967fa.accept_13_12_5_6_1_1050 51 70 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 214 2 25 35 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 70 214
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 49 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 70 214 2 24 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 70 214 (accept_3_3 47 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 70 214 2 23 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 70 214 (Polychromatic418967fa.accept_19_7_13_5_1_7125 45 70 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 70 214 2 22 35 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 70 214
  (Polychromatic418967fa.accept_11_10_4_5_1_359 43 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 70 214 2 21 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 70 214 (accept_3_3 41 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 70 214 2 20 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 70 214 (Polychromatic418967fa.accept_15_9_10_4_1_2055 39 70 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 70 214 2 19 35 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 70 214
  (Polychromatic418967fa.accept_13_11_5_6_1_519 37 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 70 214 2 18 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 70 214 (accept_3_3 35 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 70 214 2 17 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 70 214 (Polychromatic418967fa.accept_19_14_13_5_1_9905 33 70 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 70 214 2 16 35 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 70 214
  (Polychromatic418967fa.accept_19_12_13_5_1_11331 31 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 70 214 2 15 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 70 214 (accept_3_3 29 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 70 214 2 14 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 70 214 (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 70 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 214 2 13 35 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 70 214
  (Polychromatic418967fa.accept_13_12_5_6_1_1050 25 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 70 214 2 12 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 70 214 (accept_3_3 23 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 70 214 2 11 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 70 214 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 70 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 70 214 2 10 35 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 214
  (Polychromatic418967fa.accept_21_19_7_4_1_4994 19 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 70 214 2 9 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 70 214 (accept_3_3 17 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70
  214 2 8 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  70 214 (Polychromatic418967fa.accept_17_15_2_10_1_9021 15 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 70 214 2 7 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 70 214 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 70 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 214 2 6 35 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 214 (accept_3_3 11 70 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 214 2 5 35 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 214
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 70 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 70 214 2 4 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 70 214 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 70 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 214 2 3 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 214 (accept_3_3 5 70 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 70 214 2 2 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 70 214 (Polychromatic418967fa.accept_13_3_5_6_1_3192 3 70 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 214 2 1 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 214 (Polychromatic418967fa.accept_13_1_5_6_1_1048 1
  70 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 214 (allA_succ_of_accept 68 69
  214 (accept_3_3 68 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 67 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 69 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 69 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 214 (accept_3_3 65 69 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 69 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 63
  69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 214 (accept_3_3 62 69
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 214 (Polychromatic418967fa.accept_6_1_3_4_1_1
  61 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 69 214
  (Polychromatic418967fa.accept_17_9_1_10_1_2859 60 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 69 214 (accept_3_3 59 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  69 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 69 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 214 (accept_3_3 56 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 69 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 69 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 69 214 (accept_3_3 53 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  69 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 69 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 214 (accept_3_3 50 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 69 214 (accept_3_3 47 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  69 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 69 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 214 (accept_3_3 44 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 69 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 42 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 69 214 (accept_3_3 41 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  69 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 69 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 214 (accept_3_3 38 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 214
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 69 214 (accept_3_3 35 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  69 214 (Polychromatic418967fa.accept_19_15_12_5_1_8544 34 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 69 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 214 (accept_3_3 32 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 69 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 69 214 (accept_3_3 29 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  69 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 69 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 214 (accept_3_3 26 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 69 214 (accept_3_3 23 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  69 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 69 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 214 (accept_3_3 20 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 214
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 69 214 (accept_3_3 17 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  69 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 69 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 214 (accept_3_3 14 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 69 214 (accept_3_3 11 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  69 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 69 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 214 (accept_3_3 8 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 214 (accept_3_3 5 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69
  214 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 69 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 69 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 214 (accept_3_3 2 69 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 69 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 214 (allA_of_3_1 68 68 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 214 (allA_succ_of_accept 66 67 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 214 (accept_3_3 65 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 214 (accept_3_3 62 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 67 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 214 (accept_3_3 59 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 214 (Polychromatic418967fa.accept_17_7_16_10_1_1849 58 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 214 (accept_3_3 56 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 67 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 214
  (Polychromatic418967fa.accept_19_16_10_5_1_7106 54 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 214 (accept_3_3 53 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 214 (Polychromatic418967fa.accept_10_2_7_4_1_967 52 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 214 (accept_3_3 50 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 67 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 214 (accept_3_3 47 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 214 (accept_3_3 44 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 214 (Polychromatic418967fa.accept_10_3_7_4_1_584 43 67 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 214 (accept_3_3 41 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 214 (accept_3_3 38 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 67 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 214
  (Polychromatic418967fa.accept_13_10_2_6_1_1044 36 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 214 (accept_3_3 35 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 214 (Polychromatic418967fa.accept_13_8_2_6_1_2385 34 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 214 (accept_3_3 32 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 214 (Polychromatic418967fa.accept_10_1_7_4_1_968 31 67 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 214 (accept_3_3 29 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 214 (accept_3_3 26 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 67 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 214 (accept_3_3 23 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 214 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 214 (accept_3_3 20 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 67 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 214
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 214 (accept_3_3 17 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 214 (accept_3_3 14 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 214 (accept_3_3 11 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 214 (accept_3_3 8 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 214 (Polychromatic418967fa.accept_14_7_11_4_1_3455 7 67 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 214 (accept_3_3 5 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  214 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 67 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 214 (accept_3_3 2 67 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 214 (allA_succ_of_accept 65 66
  214 (accept_3_3 65 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 214 2 32 33 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 66 214
  (Polychromatic418967fa.accept_12_3_6_10_1_576 63 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 66 214 2 31 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 66 214 (Polychromatic418967fa.accept_13_9_1_6_1_510 61 66 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 214 2 30 33 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 214 (accept_3_3 59 66 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 214 2 29 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 57
  66 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 66 214 2 28 33 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 55 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 214 2 27 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 66 214 (accept_3_3 53 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 66 214 2 26 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 66 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 66 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 214 2 25 33 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 214 2 24 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 66 214 (accept_3_3 47 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 214 2 23 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 66 214 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 66 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 214 2 22 33 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 214 2 21 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 66 214 (accept_3_3 41 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 66 214 2 20 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 66 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 66 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 214 2 19 33 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 214 2 18 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 66 214 (accept_3_3 35 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 66 214 2 17 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 66 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 66 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 66 214 2 16 33 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 214 2 15 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 66 214 (accept_3_3 29 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 214 2 14 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 66 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 66 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 214 2 13 33 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 214
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 214 2 12 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 66 214 (accept_3_3 23 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 66 214 2 11 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 66 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 66 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 214 2 10 33 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 214 2 9 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 214 (accept_3_3 17 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66
  214 2 8 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  66 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 66 214 2 7 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 66 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 66 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 214 2 6 33 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 214 (accept_3_3 11 66 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 214 2 5 33 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 214
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 66 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 214 2 4 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 214 (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 66 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 214 2 3 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 214 (accept_3_3 5 66 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 66 214 2 2 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 66 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 66 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 214 2 1 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 66
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 214 (allA_of_3_1 65 65 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 214 (allA_succ_of_accept 63 64 214
  (Polychromatic418967fa.accept_19_6_7_5_1_256 63 64 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 64 214 2 31 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 64 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 64 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 214 2 30 32 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 214 (accept_3_3 59 64 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 214 2 29 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 57
  64 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 64 214 2 28 32 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 64 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 55 64 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 64 214 2 27 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 64 214 (accept_3_3 53 64 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 64 214 2 26 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 64 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 64 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 214 2 25 32 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 64 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 214 2 24 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 64 214 (accept_3_3 47 64 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 64 214 2 23 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 64 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 64 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 64 214 2 22 32 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 64 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 64 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 64 214 2 21 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 64 214 (accept_3_3 41 64 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 64 214 2 20 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 64 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 64 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 214 2 19 32 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 64 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 214 2 18 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 64 214 (accept_3_3 35 64 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 64 214 2 17 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 64 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 64 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 214 2 16 32 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 64 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 214 2 15 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 64 214 (accept_3_3 29 64 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 64 214 2 14 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 64 214 (Polychromatic418967fa.accept_22_5_20_16_1_12622 27 64 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 64 214 2 13 32 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 64 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 64 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 64 214 2 12 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 64 214 (accept_3_3 23 64 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 64 214 2 11 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 64 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 64 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 64 214 2 10 32 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 64 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 64 214 2 9 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 214 (accept_3_3 17 64 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64
  214 2 8 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  64 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 64 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 64 214 2 7 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 64 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 64 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 214 2 6 32 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 214 (accept_3_3 11 64 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 214 2 5 32 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 64 214
  (Polychromatic418967fa.accept_17_9_13_10_1_1825 9 64 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 64 214 2 4 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 64 214 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 64 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 214 2 3 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 214 (accept_3_3 5 64 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 64 214 2 2 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 64 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 64 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 214 2 1 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 214 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  64 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 214 (allA_succ_of_accept 62 63 214
  (accept_3_3 62 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 61 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 214 (Polychromatic418967fa.accept_13_8_11_6_1_1035 60 63 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 214 (accept_3_3 59 63 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 63 214 (Polychromatic418967fa.accept_11_3_8_5_1_336 58 63 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 57
  63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 214 (accept_3_3 56 63
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 214 (Polychromatic418967fa.accept_6_1_3_4_1_1
  55 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 63 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 54 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 63 214 (accept_3_3 53 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  63 214 (Polychromatic418967fa.accept_14_10_7_4_1_3453 52 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 63 214 (Polychromatic418967fa.accept_18_15_9_16_1_6029 51 63 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 214 (accept_3_3 50 63 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 63 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 63 214
  (Polychromatic418967fa.accept_18_12_9_16_1_4732 48 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 63 214 (accept_3_3 47 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  63 214 (Polychromatic418967fa.accept_11_2_8_5_1_1219 46 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 63 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 214 (accept_3_3 44 63 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 63 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 63 214 (accept_3_3 41 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  63 214 (Polychromatic418967fa.accept_17_6_12_10_1_7781 40 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 63 214 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 63 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 214 (accept_3_3 38 63 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 63 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 214
  (Polychromatic418967fa.accept_11_3_8_5_1_336 36 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 63 214 (accept_3_3 35 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  63 214 (Polychromatic418967fa.accept_13_8_11_6_1_1035 34 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 63 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 214 (accept_3_3 32 63 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 63 214 (accept_3_3 29 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  63 214 (Polychromatic418967fa.accept_20_8_3_14_1_11250 28 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 63 214 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 63 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 214 (accept_3_3 26 63 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 214
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 63 214 (accept_3_3 23 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  63 214 (Polychromatic418967fa.accept_15_7_3_4_1_574 22 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 63 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 214 (accept_3_3 20 63 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 63 214 (accept_3_3 17 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  63 214 (Polychromatic418967fa.accept_15_1_3_4_1_1217 16 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 63 214 (Polychromatic418967fa.accept_18_15_9_16_1_6029 15 63 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 214 (accept_3_3 14 63 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 214
  (Polychromatic418967fa.accept_18_12_9_16_1_4732 12 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 63 214 (accept_3_3 11 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  63 214 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 63 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 214 (accept_3_3 8 63 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 214 (accept_3_3 5 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63
  214 (Polychromatic418967fa.accept_13_4_11_6_1_1033 4 63 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 214 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 63 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 214 (accept_3_3 2 63 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 214 (allA_of_3_1 62 62 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 214 (allA_succ_of_accept 60 61 214
  (Polychromatic418967fa.accept_21_18_19_4_1_4979 60 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 214 (accept_3_3 59 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 214 (accept_3_3 56 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 61 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 214
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 214 (accept_3_3 53 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 214 (accept_3_3 50 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 214 (Polychromatic418967fa.accept_13_10_9_6_1_1026 49 61 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 214 (accept_3_3 47 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 214 (Polychromatic418967fa.accept_13_7_9_6_1_148 46 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 214 (accept_3_3 44 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 61 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 214
  (Polychromatic418967fa.accept_13_3_9_6_1_502 42 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 214 (accept_3_3 41 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 214 (accept_3_3 38 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 61 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 214
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 214 (accept_3_3 35 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 214 (accept_3_3 32 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 214 (accept_3_3 29 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 214 (accept_3_3 26 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 214 (Polychromatic418967fa.accept_10_5_1_4_1_1444 25 61 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 214
  (Polychromatic418967fa.accept_25_24_11_14_1_12621 24 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 61 214 (accept_3_3 23 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 61 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 61 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 61 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 214 (accept_3_3 20 61 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 214
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 214 (accept_3_3 17 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 214 (accept_3_3 14 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 61 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 214
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 214 (accept_3_3 11 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 214 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 214 (accept_3_3 8 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 214 (accept_3_3 5 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  214 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 61 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 214 (accept_3_3 2 61 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 61 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 214 (allA_succ_of_accept 59 60 214
  (accept_3_3 59 60 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 60 214 2 29 30 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 60 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 60 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 60 214 2 28 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 60 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 60 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 214 2 27 30 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 214 (accept_3_3 53 60 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 214 2 26 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 214 (Polychromatic418967fa.accept_18_15_6_16_1_4730
  51 60 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 214 2 25 30 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 60 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 214 2 24 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 60 214 (accept_3_3 47 60 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 60 214 2 23 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 60 214 (Polychromatic418967fa.accept_19_7_3_5_1_8585 45 60 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 214 2 22 30 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 214
  (Polychromatic418967fa.accept_21_1_18_4_1_4975 43 60 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 214 2 21 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 60 214 (accept_3_3 41 60 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 214 2 20 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 60 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 60 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 214 2 19 30 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 60 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 60 214 2 18 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 60 214 (accept_3_3 35 60 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 60 214 2 17 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 60 214 (Polychromatic418967fa.accept_17_16_9_10_1_3962 33 60 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 214 2 16 30 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 60 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 214 2 15 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 60 214 (accept_3_3 29 60 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 60 214 2 14 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 214 (Polychromatic418967fa.accept_13_1_8_6_1_1016 27 60 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 214 2 13 30 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 214
  (Polychromatic418967fa.accept_19_6_3_5_1_9897 25 60 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 60 214 2 12 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 60 214 (accept_3_3 23 60 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 60 214 2 11 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 60 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 60 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 214 2 10 30 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 60 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 214 2 9 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 214 (accept_3_3 17 60 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60
  214 2 8 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  60 214 (Polychromatic418967fa.accept_13_2_8_6_1_2390 15 60 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 60 214 2 7 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 60 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 60 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 214 2 6 30 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 214 (accept_3_3 11 60 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 214 2 5 30 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 214
  (Polychromatic418967fa.accept_21_9_18_4_1_4953 9 60 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 214 2 4 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 214 (Polychromatic418967fa.accept_19_7_3_5_1_8585 7 60 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 214 2 3 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 214 (accept_3_3 5 60 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 60 214 2 2 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 60 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 60 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 214 2 1 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 60
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 214 (allA_of_3_1 59 59 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 58 214 (allA_succ_of_accept 57 58 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 58 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 214 2 28 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 58 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 58 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 214 2 27 29 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 214 (accept_3_3 53 58 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 214 2 26 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 51
  58 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 214 2 25 29 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 214
  (Polychromatic418967fa.accept_10_9_8_4_1_970 49 58 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 214 2 24 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 58 214 (accept_3_3 47 58 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 58 214 2 23 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 58 214 (Polychromatic418967fa.accept_25_20_8_14_1_9091 45 58 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 58 214 2 22 29 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 58 214
  (Polychromatic418967fa.accept_18_7_4_16_1_2299 43 58 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 58 214 2 21 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 58 214 (accept_3_3 41 58 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 58 214 2 20 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 58 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 58 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 58 214 2 19 29 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 58 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 58 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 58 214 2 18 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 58 214 (accept_3_3 35 58 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 58 214 2 17 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 58 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 58 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 214 2 16 29 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 214
  (Polychromatic418967fa.accept_17_14_7_10_1_7808 31 58 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 214 2 15 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 58 214 (accept_3_3 29 58 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 58 214 2 14 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 58 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 58 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 214 2 13 29 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 214
  (Polychromatic418967fa.accept_15_10_13_4_1_1210 25 58 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 58 214 2 12 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 58 214 (accept_3_3 23 58 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 58 214 2 11 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 58 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 58 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 58 214 2 10 29 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 58 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 58 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 58 214 2 9 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 58 214 (accept_3_3 17 58 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58
  214 2 8 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  58 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 58 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 58 214 2 7 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 58 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 58 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 214 2 6 29 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 214 (accept_3_3 11 58 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 214 2 5 29 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 214
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 58 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 214 2 4 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 214 (Polychromatic418967fa.accept_18_7_4_16_1_2299 7 58 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 214 2 3 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 214 (accept_3_3 5 58 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 214 2 2 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 58 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 214 2 1 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 58
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 214 (allA_succ_of_accept 56 57 214
  (accept_3_3 56 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 57 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 214 (accept_3_3 53 57 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 57 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 214 (accept_3_3 50 57
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 214 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 214
  (Polychromatic418967fa.accept_21_6_15_4_1_5021 48 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 57 214 (accept_3_3 47 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  57 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 57 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 214 (accept_3_3 44 57 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 57 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 214
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 214 (accept_3_3 41 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 214 (accept_3_3 38 57 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 214
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 36 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 214 (accept_3_3 35 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 214 (Polychromatic418967fa.accept_16_2_9_6_1_4441 34 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 57 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 214 (accept_3_3 32 57 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 214
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 214 (accept_3_3 29 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 214 (accept_3_3 26 57 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 214 (accept_3_3 23 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 214 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 57 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 214 (accept_3_3 20 57 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 214 (accept_3_3 17 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 214 (Polychromatic418967fa.accept_13_3_5_6_1_3192 16 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 214 (accept_3_3 14 57 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 214 (accept_3_3 11 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 214 (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 57 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 214 (accept_3_3 8 57 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 214
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 214 (accept_3_3 5 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  214 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 57 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 214 (accept_3_3 2 57 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 214 (allA_of_3_1 56 56 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 214
  (allA_succ_of_accept 54 55 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 55 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 214 (accept_3_3 53 55 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 55 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 51
  55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 214 (accept_3_3 50 55
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 214 (Polychromatic418967fa.accept_4_1_3_2_1_3
  49 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 214 (accept_3_3 47 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 214 (Polychromatic418967fa.accept_10_6_5_4_1_571 46 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 55 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 214 (accept_3_3 44 55 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 214 (Polychromatic418967fa.accept_15_13_10_4_1_1232 43 55 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 214 (accept_3_3 41 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 214 (accept_3_3 38 55 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 214
  (Polychromatic418967fa.accept_10_6_5_4_1_571 36 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 214 (accept_3_3 35 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 214 (Polychromatic418967fa.accept_19_15_17_5_1_3052 34 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 55 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 214 (accept_3_3 32 55 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 55 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 214 (accept_3_3 29 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 214 (accept_3_3 26 55 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 55 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 214 (accept_3_3 23 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 214 (accept_3_3 20 55 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 55 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 214
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 18 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 214 (accept_3_3 17 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 55 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 214 (accept_3_3 14 55 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 214 (accept_3_3 11 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 214 (accept_3_3 8 55 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 214 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 55 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 214 (accept_3_3 5 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  214 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 55 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 214 (accept_3_3 2 55 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 214)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 214 (allA_succ_of_accept 53 54 214 (accept_3_3 53 54 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 214 2 26 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 54 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 54 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 214 2 25 27 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 214
  (Polychromatic418967fa.accept_13_10_2_6_1_1044 49 54 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 54 214 2 24 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 54 214 (accept_3_3 47 54 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 54 214 2 23 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 54 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 54 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 214 2 22 27 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 214
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 54 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 214 2 21 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 54 214 (accept_3_3 41 54 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 54 214 2 20 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 54 214 (Polychromatic418967fa.accept_11_6_10_5_1_341 39 54 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 214 2 19 27 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 54 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 214 2 18 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 54 214 (accept_3_3 35 54 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 214 2 17 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 54 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 54 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 214 2 16 27 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 214
  (Polychromatic418967fa.accept_19_12_16_5_1_12620 31 54 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 54 214 2 15 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 54 214 (accept_3_3 29 54 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 54 214 2 14 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 54 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 54 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 214 2 13 27 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 214
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 25 54 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 214 2 12 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 214 (accept_3_3 23 54 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 54 214 2 11 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 54 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 54 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 214 2 10 27 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 214
  (Polychromatic418967fa.accept_21_19_12_4_1_8134 19 54 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 214 2 9 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 214 (accept_3_3 17 54 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54
  214 2 8 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  54 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 54 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 54 214 2 7 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 54 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 54 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 214 2 6 27 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 214 (accept_3_3 11 54 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 214 2 5 27 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 54 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 54 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 54 214 2 4 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 54 214 (Polychromatic418967fa.accept_17_7_3_10_1_2881 7 54 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 214 2 3 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 214 (accept_3_3 5 54 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 54 214 2 2 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 54 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 54 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 214 2 1 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 54
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 214 (allA_of_3_1 53 53 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 214 (allA_succ_of_accept 51 52 214 (Polychromatic418967fa.accept_16_3_4_6_1_6798 51
  52 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 214 2 25 26 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 52 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 52 214 2 24 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 52 214 (accept_3_3 47 52 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 52 214 2 23 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 52 214 (Polychromatic418967fa.accept_16_13_4_6_1_2322 45 52 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 52 214 2 22 26 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 52 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 214 2 21 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 52 214 (accept_3_3 41 52 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 52 214 2 20 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 52 214 (Polychromatic418967fa.accept_32_7_20_22_1_12619 39 52 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 52 214 2 19 26 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 52 214
  (Polychromatic418967fa.accept_10_7_2_4_1_569 37 52 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 52 214 2 18 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 52 214 (accept_3_3 35 52 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 52 214 2 17 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 52 214 (Polychromatic418967fa.accept_15_3_7_4_1_1225 33 52 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 214 2 16 26 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 52 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 52 214 2 15 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 52 214 (accept_3_3 29 52 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 52 214 2 14 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 52 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 52 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 214 2 13 26 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 214
  (Polychromatic418967fa.accept_11_3_8_5_1_336 25 52 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 52 214 2 12 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 52 214 (accept_3_3 23 52 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 52 214 2 11 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 52 214 (Polychromatic418967fa.accept_14_7_10_4_1_130 21 52 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 214 2 10 26 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 52 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 214 2 9 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 214 (accept_3_3 17 52 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52
  214 2 8 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  52 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 52 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 52 214 2 7 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 52 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 52 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 214 2 6 26 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 214 (accept_3_3 11 52 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 214 2 5 26 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 52 214
  (Polychromatic418967fa.accept_17_9_1_10_1_2859 9 52 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 52 214 2 4 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 52 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 52 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 214 2 3 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 214 (accept_3_3 5 52 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 52 214 2 2 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 52 214 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 52 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 214 2 1 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 52
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  214)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 214 (allA_succ_of_accept 50 51 214 (accept_3_3
  50 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 51 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 214 (accept_3_3 47 51 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 51 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  51 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 214 (accept_3_3 44 51
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 214 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 51 214
  (Polychromatic418967fa.accept_11_9_7_5_1_749 42 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 51 214 (accept_3_3 41 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  51 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 51 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 51 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 214 (accept_3_3 38 51 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 214
  (Polychromatic418967fa.accept_13_10_12_6_1_991 36 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 214 (accept_3_3 35 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  51 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 51 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 214 (accept_3_3 32 51 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 214 (accept_3_3 29 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 51 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 214 (accept_3_3 26 51 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 214
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 24 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 214 (accept_3_3 23 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  51 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 214 (accept_3_3 20 51 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 214 (accept_3_3 17 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  51 214 (Polychromatic418967fa.accept_14_2_9_4_1_1735 16 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 214 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 51 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 214 (accept_3_3 14 51 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 214 (accept_3_3 11 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 214 (accept_3_3 8 51 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 214 (accept_3_3 5 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  214 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 51 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 51 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 214 (accept_3_3 2 51 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 214)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 214 (allA_of_3_1 50 50 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 214
  (allA_succ_of_accept 48 49 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 49 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 214 (accept_3_3 47 49 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 49 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 45
  49 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 214 (accept_3_3 44 49
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 214 (Polychromatic418967fa.accept_4_3_1_2_1_62
  43 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 214 (accept_3_3 41 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 214 (accept_3_3 38 49 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 49 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 214
  (Polychromatic418967fa.accept_17_2_15_10_1_5171 36 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 214 (accept_3_3 35 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 214 (Polychromatic418967fa.accept_16_2_1_6_1_2342 34 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 214 (accept_3_3 32 49 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 214 (accept_3_3 29 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 214 (accept_3_3 26 49 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 214 (Polychromatic418967fa.accept_10_5_9_4_1_1420 25 49 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 214 (accept_3_3 23 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 214 (Polychromatic418967fa.accept_13_9_10_6_1_1028 22 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 214 (accept_3_3 20 49 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 214
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 214 (accept_3_3 17 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 214 (accept_3_3 14 49 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 214 (Polychromatic418967fa.accept_10_3_9_4_1_960 13 49 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 214 (accept_3_3 11 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 214 (accept_3_3 8 49 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 214 (accept_3_3 5 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  214 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 49 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 214 (accept_3_3 2 49 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 49 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 214)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 214 (allA_succ_of_accept 47 48 214 (accept_3_3 47 48 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 214 2 23 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 48 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 48 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 214 2 22 24 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 214
  (Polychromatic418967fa.accept_11_10_4_5_1_359 43 48 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 48 214 2 21 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 48 214 (accept_3_3 41 48 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 48 214 2 20 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 48 214 (Polychromatic418967fa.accept_10_9_8_4_1_970 39 48 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 214 2 19 24 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 48 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 214 2 18 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 48 214 (accept_3_3 35 48 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 48 214 2 17 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 48 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 48 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 214 2 16 24 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 48 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 214 2 15 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 48 214 (accept_3_3 29 48 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 48 214 2 14 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 48 214 (Polychromatic418967fa.accept_13_1_9_6_1_146 27 48 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 214 2 13 24 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 214
  (Polychromatic418967fa.accept_20_5_8_14_1_5341 25 48 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 214 2 12 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 48 214 (accept_3_3 23 48 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 48 214 2 11 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 48 214 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 48 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 214 2 10 24 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 48 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 214 2 9 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 214 (accept_3_3 17 48 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48
  214 2 8 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  48 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 48 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 48 214 2 7 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 48 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 48 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 214 2 6 24 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 214 (accept_3_3 11 48 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 214 2 5 24 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 48 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 214 2 4 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 214 (Polychromatic418967fa.accept_13_7_9_6_1_148 7 48 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 214 2 3 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 214 (accept_3_3 5 48 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 48 214 2 2 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 48 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 48 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 214 2 1 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 48
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  214)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 214 (allA_of_3_1 47 47 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 46 214 (allA_succ_of_accept 45 46 214 (Polychromatic418967fa.accept_10_5_6_4_1_64 45
  46 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 46 214 2 22 23 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 46 214
  (Polychromatic418967fa.accept_13_4_7_6_1_2359 43 46 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 46 214 2 21 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 46 214 (accept_3_3 41 46 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 46 214 2 20 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 46 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 46 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 214 2 19 23 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 214
  (Polychromatic418967fa.accept_18_1_10_16_1_566 37 46 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 214 2 18 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 46 214 (accept_3_3 35 46 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 46 214 2 17 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 46 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 46 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 214 2 16 23 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 46 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 46 214 2 15 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 46 214 (accept_3_3 29 46 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 46 214 2 14 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 46 214 (Polychromatic418967fa.accept_13_1_7_6_1_142 27 46 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 214 2 13 23 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 214
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 46 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 46 214 2 12 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 46 214 (accept_3_3 23 46 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 46 214 2 11 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 46 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 46 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 214 2 10 23 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 214
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 46 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 214 2 9 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 214 (accept_3_3 17 46 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  214 2 8 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 46 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 214 2 7 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 46 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 46 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 214 2 6 23 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 214 (accept_3_3 11 46 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 214 2 5 23 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 214
  (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 46 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 214 2 4 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 214 (Polychromatic418967fa.accept_25_7_21_14_1_12618 7 46 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 214 2 3 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 214 (accept_3_3 5 46 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 214 2 2 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 46 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 214 2 1 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 214 (Polychromatic418967fa.accept_13_1_7_6_1_142 1
  46 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  214)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 214 (allA_succ_of_accept 44 45 214 (accept_3_3 44 45
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 214 (Polychromatic418967fa.accept_4_3_1_2_1_62
  43 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 42 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 214 (accept_3_3 41 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  45 214 (Polychromatic418967fa.accept_19_2_7_5_1_3067 40 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 45 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 45 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 214 (accept_3_3 38 45 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 214 (accept_3_3 35 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 214 (Polychromatic418967fa.accept_18_15_9_16_1_6029 33 45 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 214 (accept_3_3 32 45 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 214 (accept_3_3 29 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 214 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 214 (accept_3_3 26 45 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 214
  (Polychromatic418967fa.accept_23_1_22_7_1_12617 24 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 214 (accept_3_3 23 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 214 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 45 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 214 (accept_3_3 20 45 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 214 (accept_3_3 17 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 214 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 45 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 214 (accept_3_3 14 45 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 214
  (Polychromatic418967fa.accept_18_12_9_16_1_4732 12 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 214 (accept_3_3 11 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 214 (Polychromatic418967fa.accept_19_10_7_5_1_5653 10 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 214 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 45 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 214 (accept_3_3 8 45 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 214 (accept_3_3 5 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  214 (Polychromatic418967fa.accept_16_4_13_6_1_4417 4 45 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 214 (accept_3_3 2 45 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 214)))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 44 214 (allA_of_3_1 44 44 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 214
  (allA_succ_of_accept 42 43 214 (Polychromatic418967fa.accept_22_20_21_16_1_12616 42 43 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 214 (accept_3_3 41 43 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 43 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 214 (accept_3_3 38 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 214 (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 43 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 214 (accept_3_3 35 43 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 214 (Polychromatic418967fa.accept_16_2_11_6_1_737 34 43 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 214 (accept_3_3 32 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 214 (Polychromatic418967fa.accept_17_13_9_10_1_2888 30 43 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 214 (accept_3_3 29 43 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 214 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 43 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 214 (accept_3_3 26 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 43 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 214 (accept_3_3 23 43 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 214 (Polychromatic418967fa.accept_13_9_4_6_1_1005 22 43 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 214 (accept_3_3 20 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 214 (Polychromatic418967fa.accept_13_5_4_6_1_2371 18 43 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 214 (accept_3_3 17 43 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 43 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 214 (accept_3_3 14 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 43 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 214 (accept_3_3 11 43 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 43 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 214 (accept_3_3 8 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  214 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 43 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 214 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 43 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 214 (accept_3_3 5 43 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 214 (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 43 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 214 (accept_3_3 2 43 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43
  214))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 214 (allA_succ_of_accept 41 42 214 (accept_3_3 41 42 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 214 2 20 21 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 42 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 42 214 2 19 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 42 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 42 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 214 2 18 21 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 214 (accept_3_3 35 42 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 214 2 17 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085
  33 42 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 214 2 16 21 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 42 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 214 2 15 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 42 214 (accept_3_3 29 42 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 214 2 14 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 42 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 42 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 214 2 13 21 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 214
  (Polychromatic418967fa.accept_19_6_4_5_1_5650 25 42 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 214 2 12 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 42 214 (accept_3_3 23 42 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 214 2 11 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 42 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 42 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 42 214 2 10 21 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 42 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 214 2 9 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 214 (accept_3_3 17 42 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42
  214 2 8 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  42 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 42 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 42 214 2 7 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 42 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 42 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 214 2 6 21 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 214 (accept_3_3 11 42 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 214 2 5 21 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 214
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 42 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 214 2 4 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 42 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 214 2 3 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 214 (accept_3_3 5 42 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 42 214 2 2 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 42 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 42 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 214 2 1 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 42
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  214)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 214 (allA_of_3_1 41 41 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 40 214 (allA_succ_of_accept 39 40 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 40 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 214 2 19 20 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 40 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 40 214 2 18 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 40 214 (accept_3_3 35 40 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 40 214 2 17 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 40 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 40 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 214 2 16 20 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 214
  (Polychromatic418967fa.accept_11_9_7_5_1_749 31 40 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 214 2 15 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 40 214 (accept_3_3 29 40 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 40 214 2 14 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 40 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 40 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 214 2 13 20 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 40 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 40 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 40 214 2 12 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 40 214 (accept_3_3 23 40 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 40 214 2 11 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 40 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 40 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 214 2 10 20 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 40 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 40 214 2 9 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 40 214 (accept_3_3 17 40 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40
  214 2 8 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  40 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 40 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 40 214 2 7 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 40 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 40 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 214 2 6 20 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 214 (accept_3_3 11 40 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 214 2 5 20 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 40 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 214 2 4 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 214 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 40 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 214 2 3 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 214 (accept_3_3 5 40 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 40 214 2 2 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 40 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 40 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 214 2 1 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 40
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  214)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 214 (allA_succ_of_accept 38 39 214 (accept_3_3 38 39 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  39 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 214
  (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 214 (accept_3_3 35 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  39 214 (Polychromatic418967fa.accept_11_1_6_5_1_1732 34 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 214 (accept_3_3 32 39 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 214 (accept_3_3 29 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 214 (Polychromatic418967fa.accept_15_12_9_4_1_3898 27 39 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 214 (accept_3_3 26 39 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 214
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 214 (accept_3_3 23 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 214 (accept_3_3 20 39 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 214
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 214 (accept_3_3 17 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 214 (Polychromatic418967fa.accept_19_16_1_5_1_3084 16 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 39 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 214 (accept_3_3 14 39 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 214
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 214 (accept_3_3 11 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 214 (accept_3_3 8 39 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 214
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 214 (accept_3_3 5 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  214 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 39 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 214 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 39 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 214 (accept_3_3 2 39 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 214))))))))))))))))))))))))))))))))))))))) (allB_succ 38 214
  (allA_of_3_1 38 38 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 214 (allA_succ_of_accept 36 37 214
  (Polychromatic418967fa.accept_16_4_5_6_1_8071 36 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 214 (accept_3_3 35 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 214 (accept_3_3 32 37 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 37 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 214 (accept_3_3 29 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 214 (accept_3_3 26 37 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 214 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 37 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 214 (accept_3_3 23 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 214 (accept_3_3 20 37 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 214
  (Polychromatic418967fa.accept_13_5_11_6_1_505 18 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 214 (accept_3_3 17 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 214 (accept_3_3 14 37 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 37 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 214 (accept_3_3 11 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 214 (Polychromatic418967fa.accept_11_10_4_5_1_359 10 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 214 (accept_3_3 8 37 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 214 (accept_3_3 5 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  214 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 37 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 214 (accept_3_3 2 37 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 214 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 37 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 214))))))))))))))))))))))))))))))))))))) (allB_succ 36 214
  (allA_succ_of_accept 35 36 214 (accept_3_3 35 36 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36
  214 2 17 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 36 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 36 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 36 214 2 16 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 36 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 36 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 214 2 15 18 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 214 (accept_3_3 29 36 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 214 2 14 18 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 214
  (Polychromatic418967fa.accept_16_11_4_6_1_4422 27 36 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 214 2 13 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 36 214 (Polychromatic418967fa.accept_10_5_6_4_1_64 25 36 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 214 2 12 18 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 214 (accept_3_3 23 36 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 214 2 11 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 214 (Polychromatic418967fa.accept_16_5_4_6_1_3349
  21 36 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 214 2 10 18 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 36 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 214 2 9 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 214 (accept_3_3 17 36 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36
  214 2 8 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  36 214 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 36 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 36 214 2 7 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 36 214 (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 36 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 214 2 6 18 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 214 (accept_3_3 11 36 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 214 2 5 18 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 36 214
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 36 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 36 214 2 4 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 214 (Polychromatic418967fa.accept_19_7_17_5_1_3081 7 36 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 214 2 3 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 214 (accept_3_3 5 36 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 36 214 2 2 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 36 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 36 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 214 2 1 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 214 (Polychromatic418967fa.accept_23_1_13_7_1_9355 1
  36 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  214)))))))))))))))))))))))))))))))))))) (allB_succ 35 214 (allA_of_3_1 35 35 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 34 214 (allA_succ_of_accept 33 34 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 34 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 34 214 2 16 17 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 34 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 34 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 34 214 2 15 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 34 214 (accept_3_3 29 34 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 34 214 2 14 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 34 214 (Polychromatic418967fa.accept_13_1_8_6_1_1016 27 34 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 214 2 13 17 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 214
  (Polychromatic418967fa.accept_16_9_2_6_1_4434 25 34 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 214 2 12 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 34 214 (accept_3_3 23 34 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 34 214 2 11 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 34 214 (Polychromatic418967fa.accept_26_21_8_6_1_12615 21 34 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 34 214 2 10 17 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 34 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 34 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 34 214 2 9 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 34 214 (accept_3_3 17 34 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34
  214 2 8 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  34 214 (Polychromatic418967fa.accept_13_2_8_6_1_2390 15 34 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 34 214 2 7 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 34 214 (Polychromatic418967fa.accept_26_13_8_6_1_12614 13 34 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 214 2 6 17 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 214 (accept_3_3 11 34 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 214 2 5 17 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 34 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 214 2 4 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 214 (Polychromatic418967fa.accept_21_7_13_4_1_2169 7 34 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 214 2 3 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 214 (accept_3_3 5 34 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 214 2 2 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 34 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 214 2 1 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 214 (Polychromatic418967fa.accept_13_1_8_6_1_1016 1
  34 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 214))))))))))))))))))))))))))))))))))
  (allB_succ 33 214 (allA_succ_of_accept 32 33 214 (accept_3_3 32 33 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 33 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 33 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 214 (accept_3_3 29 33 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 28
  33 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 214 (accept_3_3 26 33 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 214 (Polychromatic418967fa.accept_17_7_16_10_1_1849 24 33 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 214 (accept_3_3 23 33 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 33 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 33 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 214 (accept_3_3 20 33 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 214 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 33 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 214 (accept_3_3 17 33 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 33 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 214 (accept_3_3 14 33 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 33 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 214 (accept_3_3 11 33 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 33 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 33 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 214 (accept_3_3 8 33 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 33 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 214 (accept_3_3 5 33 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 33 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 214 (accept_3_3 2 33 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 214)))))))))))))))))))))))))))))))))
  (allB_succ 32 214 (allA_of_3_1 32 32 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 214
  (allA_succ_of_accept 30 31 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 31 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 214 (accept_3_3 29 31 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 31 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 27
  31 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 214 (accept_3_3 26 31
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 214 (Polychromatic418967fa.accept_4_1_3_2_1_3
  25 31 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 31 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 214 (accept_3_3 23 31 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 31 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 214 (accept_3_3 20 31 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 31 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 214
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 31 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 214 (accept_3_3 17 31 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 31 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 214 (accept_3_3 14 31 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 31 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 214 (accept_3_3 11 31 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 31 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 214 (accept_3_3 8 31 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 214 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 31 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 31 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 214 (accept_3_3 5 31 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  214 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 31 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 214 (accept_3_3 2 31 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 214))))))))))))))))))))))))))))))) (allB_succ 30 214
  (allA_succ_of_accept 29 30 214 (accept_3_3 29 30 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30
  214 2 14 15 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  27 30 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 30 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 30 214 2 13 15 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 30 214 (Polychromatic418967fa.accept_11_3_8_5_1_336 25 30 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 214 2 12 15 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 214 (accept_3_3 23 30 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 214 2 11 15 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 214
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 30 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 214 2 10 15 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 30 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 30 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 214 2 9 15 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 214 (accept_3_3 17 30 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 214 2 8 15 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 15
  30 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 214 2 7 15 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 30 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 214 2 6 15 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 214 (accept_3_3 11 30 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30
  214 2 5 15 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  30 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 30 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 30 214 2 4 15 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 30 214 (Polychromatic418967fa.accept_13_7_4_6_1_3221 7 30 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 214 2 3 15 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 214 (accept_3_3 5 30 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 214 2 2 15 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 30 214 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 30 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 214 2 1 15 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 30 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 30 214)))))))))))))))))))))))))))))) (allB_succ 29 214 (allA_of_3_1 29 29 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 28 214 (allA_succ_of_accept 27 28 214 (Polychromatic418967fa.accept_13_1_2_6_1_515 27 28 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 214 2 13 14 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 28 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 28 214 2 12 14 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 28 214 (accept_3_3 23 28 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 28 214 2 11 14 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 28 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 28 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 214 2 10 14 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 214
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 28 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 214 2 9 14 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 214 (accept_3_3 17 28 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28
  214 2 8 14 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  28 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 28 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 28 214 2 7 14 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 28 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 28 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 214 2 6 14 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 214 (accept_3_3 11 28 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 214 2 5 14 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 214
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 28 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 28 214 2 4 14 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 28 214 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 28 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 214 2 3 14 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 214 (accept_3_3 5 28 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 28 214 2 2 14 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 28 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 28 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 214 2 1 14 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 214 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1
  28 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 214))))))))))))))))))))))))))))
  (allB_succ 27 214 (allA_succ_of_accept 26 27 214 (accept_3_3 26 27 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 27 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 214 (accept_3_3 23 27 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 214 (Polychromatic418967fa.accept_10_2_7_4_1_967
  22 27 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 214 (accept_3_3 20 27 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 214 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 27 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 214 (accept_3_3 17 27 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 27 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 214
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 15 27 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 214 (accept_3_3 14 27 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 27 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 214 (accept_3_3 11 27 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 27 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 214 (accept_3_3 8 27 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  214 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 27 214 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 27 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 214 (accept_3_3 5 27 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 27 214 (Polychromatic418967fa.accept_16_4_11_6_1_5591 4 27 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 27
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 214 (accept_3_3 2 27 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 214)))))))))))))))))))))))))))
  (allB_succ 26 214 (allA_of_3_1 26 26 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 214
  (allA_succ_of_accept 24 25 214 (Polychromatic418967fa.accept_15_9_10_4_1_2055 24 25 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 214 (accept_3_3 23 25 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 214 (Polychromatic418967fa.accept_14_8_11_4_1_3438 22 25 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 25 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 25 214 (accept_3_3 20 25 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  25 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 25 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 25 214 (Polychromatic418967fa.accept_13_5_12_6_1_508 18 25 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 214 (accept_3_3 17 25 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 214 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 25 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 25 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 214 (accept_3_3 14 25 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 214 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 25 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 214 (Polychromatic418967fa.accept_17_12_8_10_1_6440 12 25 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 214 (accept_3_3 11 25 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 214 (Polychromatic418967fa.accept_13_10_12_6_1_991 10 25
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 214 (accept_3_3 8 25 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 25 214 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 25 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 214 (accept_3_3 5 25 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 25 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 25 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 214 (accept_3_3 2 25 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 214 (Polychromatic418967fa.accept_10_1_5_4_1_276 1
  25 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 214)))))))))))))))))))))))))
  (allB_succ 24 214 (allA_succ_of_accept 23 24 214 (accept_3_3 23 24 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 24 214 2 11 12 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 24 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 24 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 24 214 2 10 12 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 24 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 24 214 2 9 12 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 24 214 (accept_3_3 17 24 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24
  214 2 8 12 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  24 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 24 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 24 214 2 7 12 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 24 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 24 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 214 2 6 12 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 214 (accept_3_3 11 24 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 214 2 5 12 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 214
  (Polychromatic418967fa.accept_20_9_4_14_1_8344 9 24 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 214 2 4 12 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 214 (Polychromatic418967fa.accept_14_7_10_4_1_130 7 24 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 214 2 3 12 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 214 (accept_3_3 5 24 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 24 214 2 2 12 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 24 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 24 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 214 2 1 12 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 24
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 214)))))))))))))))))))))))) (allB_succ
  23 214 (allA_of_3_1 23 23 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 214 (allA_succ_of_accept 21 22
  214 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 22 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 214 2 10 11 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 22 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 22 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 214 2 9 11 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 214 (accept_3_3 17 22 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22 214 2 8 11 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 22 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 15
  22 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 214 2 7 11 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 214
  (Polychromatic418967fa.accept_17_13_5_10_1_2839 13 22 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 22 214 2 6 11 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 22 214 (accept_3_3 11 22 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22
  214 2 5 11 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  22 214 (Polychromatic418967fa.accept_25_9_22_14_1_12613 9 22 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 22 214 2 4 11 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 22 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 22 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 214 2 3 11 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 214 (accept_3_3 5 22 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 214 2 2 11 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 22 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 22 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 214 2 1 11 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 22 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 214)))))))))))))))))))))) (allB_succ 21 214 (allA_succ_of_accept 20 21 214 (accept_3_3 20 21 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 21 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 21 214 (accept_3_3 17 21 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  21 214 (Polychromatic418967fa.accept_19_16_2_5_1_5681 16 21 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 21 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 214 (accept_3_3 14 21 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 214
  (Polychromatic418967fa.accept_27_12_21_25_1_12612 12 21 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 214 (accept_3_3 11 21 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 21 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 214 (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 21 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 214 (accept_3_3 8 21 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 214
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 21 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 214 (accept_3_3 5 21 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  214 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 21 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 21 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 214 (accept_3_3 2 21 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 21 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 214))))))))))))))))))))) (allB_succ 20 214 (allA_of_3_1 20 20
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 214 (allA_succ_of_accept 18 19 214
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 19 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 214 (accept_3_3 17 19 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 19 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 214 (accept_3_3 14 19 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 19 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 214 (accept_3_3 11 19 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 214 (Polychromatic418967fa.accept_18_10_1_16_1_579 10 19 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 214 (accept_3_3 8 19 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 214 (Polychromatic418967fa.accept_18_7_1_16_1_578 7 19 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 19 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 214 (accept_3_3 5 19 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  214 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 19 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 214 (accept_3_3 2 19 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 214))))))))))))))))))) (allB_succ 18 214 (allA_succ_of_accept 17
  18 214 (accept_3_3 17 18 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 214 2 8 9 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 214
  (Polychromatic418967fa.accept_12_3_6_10_1_576 15 18 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 214 2 7 9 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 214 (Polychromatic418967fa.accept_19_13_18_5_1_8619 13 18 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 214 2 6 9 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 214 (accept_3_3 11 18 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 214 2 5 9 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 214 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 18 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 214 2 4 9 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 214 (Polychromatic418967fa.accept_15_7_3_4_1_574 7
  18 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 214 2 3 9 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 214 (accept_3_3 5 18
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 214 2 2 9 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 214
  (Polychromatic418967fa.accept_12_3_6_10_1_576 3 18 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 214 2 1 9 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 214 (Polychromatic418967fa.accept_13_1_5_6_1_1048 1 18 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 214)))))))))))))))))) (allB_succ 17 214 (allA_of_3_1 17 17 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 214 (allA_succ_of_accept 15 16 214
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 16 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 214 2 7 8 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 16 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 214 2 6 8 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 214 (accept_3_3 11 16 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 214 2 5 8 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 214 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 16 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 214 2 4 8 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 214 (Polychromatic418967fa.accept_12_7_4_10_1_572 7
  16 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 214 2 3 8 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 214 (accept_3_3 5 16
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 214 2 2 8 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 214
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 3 16 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 214 2 1 8 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 214 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 16 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 214)))))))))))))))) (allB_succ 15 214 (allA_succ_of_accept 14 15 214
  (accept_3_3 14 15 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 15 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 214 (accept_3_3 11 15 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 15 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 214 (accept_3_3 8 15 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 214
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 15 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 214 (accept_3_3 5 15 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  214 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 15 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 15 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 214 (accept_3_3 2 15 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 214))))))))))))))) (allB_succ 14 214 (allA_of_3_1 14 14 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 214 (allA_succ_of_accept 12 13 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 13 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 214 (accept_3_3 11 13 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 13 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 214 (accept_3_3 8 13 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 13 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 214 (accept_3_3 5 13 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  214 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 13 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 214 (accept_3_3 2 13 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 13 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 214))))))))))))) (allB_succ 12 214
  (allA_succ_of_accept 11 12 214 (accept_3_3 11 12 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12
  214 2 5 6 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  12 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 12 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 12 214 2 4 6 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 12 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 12 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 214 2 3 6 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 214 (accept_3_3 5 12 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 214 2 2 6 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 12 214 (Polychromatic418967fa.accept_21_3_12_4_1_8116 3 12 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 214 2 1 6 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 214
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 12 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 214)))))))))))) (allB_succ 11 214 (allA_of_3_1 11 11 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 214 (allA_succ_of_accept 9 10 214 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 10 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 214 2 4 5 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 214
  (Polychromatic418967fa.accept_14_7_10_4_1_130 7 10 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 10 214 2 3 5 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 10 214 (accept_3_3 5 10 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 214
  2 2 5 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10
  214 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 10 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 10 214 2 1 5 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 10 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 10 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 10 214)))))))))) (allB_succ 9 214 (allA_succ_of_accept 8 9 214 (accept_3_3 8
  9 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 214 (Polychromatic418967fa.accept_4_3_1_2_1_62
  7 9 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 9 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 214 (accept_3_3 5 9 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 214
  (Polychromatic418967fa.accept_13_4_9_6_1_2376 4 9 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 214 (accept_3_3 2 9 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 214))))))))) (allB_succ 8 214 (allA_of_3_1 8 8 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 214 (allA_succ_of_accept 6 7 214
  (Polychromatic418967fa.accept_19_6_7_5_1_256 6 7 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 214 (accept_3_3 5 7 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 214
  (Polychromatic418967fa.accept_12_4_7_10_1_563 4 7 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 214 (accept_3_3 2 7 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 214))))))) (allB_succ 6 214 (allA_succ_of_accept 5 6 214
  (accept_3_3 5 6 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 214 2 2 3 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 6 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 214 2 1 3 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 6 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 214)))))) (allB_succ 5 214 (allA_of_3_1 5 5 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 214 (allA_succ_of_accept 3 4 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 4 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 214 2 1 2 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 4 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 214)))) (allB_succ 3 214 (allA_succ_of_accept 2 3 214 (accept_3_3 2 3 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 214))) (allB_succ 2 214 (allA_of_3_1 2 2 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


