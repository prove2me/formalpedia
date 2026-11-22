-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch246_Segment001
-- name    : Polychromatic418967fa_Branch246_Segment001
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:42:22.877307+00:00
-- url     : https://prove2.me/theorems/be9175ed-1f1c-4e48-9ab3-7853e0355cd6
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch246_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_246_segment_001 : allB 145 246 :=
  allB_succ' 103 144 246 (Eq.refl Bool.true) (allA_succ_of_gcd 102 144 246 6 17 24 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 144 246
  (Polychromatic418967fa.accept_7_3_4_1_1_71 101 144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 144 246 2 50 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 99 144 246 3 33 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 144 246 2 49 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 144 246 (Polychromatic418967fa.accept_21_13_18_15_1_2837 97 144
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 144 246 6 16 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 144 246
  (Polychromatic418967fa.accept_10_5_4_6_1_319 95 144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 144 246 2 47 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 93 144 246 3 31 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 144 246 2 46 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 144 246 (Polychromatic418967fa.accept_15_1_9_6_1_1323 91 144
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 144 246 6 15 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 144 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 89 144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 144 246 2 44 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 87 144 246 3 29 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 144 246 2 43 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 144 246 (Polychromatic418967fa.accept_10_5_4_6_1_319 85 144 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 144 246 6 14 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 144 246
  (Polychromatic418967fa.accept_13_5_1_12_1_740 83 144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 144 246 2 41 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 144 246 3 27 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 144 246 2 40 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 144 246 (Polychromatic418967fa.accept_15_4_9_6_1_627 79 144 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 144 246 6 13 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 144 246
  (Polychromatic418967fa.accept_19_1_11_18_1_10841 77 144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 144 246 2 38 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 75 144 246 3 25 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 144 246 2 37 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 144 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 73
  144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 144 246 6 12 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 144 246
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 71 144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 144 246 2 35 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 144 246 3 23 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 144 246 2 34 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 144 246 (Polychromatic418967fa.accept_13_2_1_12_1_1326 67 144
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 144 246 6 11 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 144 246
  (Polychromatic418967fa.accept_10_5_4_6_1_319 65 144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 144 246 2 32 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 144 246 3 21 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 144 246 2 31 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 144 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 144 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 144 246 6 10 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 144 246
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 144 246 2 29 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 144 246 3 19 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 144 246 2 28 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 144 246 (Polychromatic418967fa.accept_10_5_4_6_1_319 55 144 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 144 246 6 9 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 144 246
  (Polychromatic418967fa.accept_14_11_4_8_1_664 53 144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 144 246 2 26 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 144 246 3 17 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 144 246 2 25 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 246 (Polychromatic418967fa.accept_15_4_9_6_1_627 49 144 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 144 246 6 8 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 144 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 144 246 2 23 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 144 246 3 15 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 144 246 2 22 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 246 (Polychromatic418967fa.accept_21_1_18_15_1_11934 43 144
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 144 246 6 7 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 144 246
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 41 144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 144 246 2 20 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 144 246 3 13 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 144 246 2 19 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 246 (Polychromatic418967fa.accept_13_11_1_12_1_742 37 144
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 144 246 6 6 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 144 246
  (Polychromatic418967fa.accept_10_5_4_6_1_319 35 144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 144 246 2 17 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 144 246 3 11 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 144 246 2 16 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 144 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 144 246 6 5 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 144 246
  (Polychromatic418967fa.accept_15_14_9_6_1_5093 29 144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 144 246 2 14 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 144 246 3 9 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 144 246 2 13 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 144 246 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 144 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 144 246 6 4 24 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 144 246
  (Polychromatic418967fa.accept_19_4_11_18_1_3909 23 144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 144 246 2 11 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 144 246 3 7 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 20 144 246 2 10 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 144 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 246 6 3 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 246
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 144 246 2 8 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 144 246 3 5 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 144 246 2 7 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 144 246 (Polychromatic418967fa.accept_21_13_18_15_1_2837 13 144 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 246 6 2 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 246
  (Polychromatic418967fa.accept_13_11_1_12_1_742 11 144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 246 2 5 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 144 246 3 3 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 144 246 2 4 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 144 246 (Polychromatic418967fa.accept_19_7_11_18_1_6680 7 144 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 246 6 1 24 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 144 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 144 246 2 2 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 144 246 3 1 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 144 246 2 1 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 144 246 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 144 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 143 246 (Eq.refl Bool.true) (allA_succ_of_accept 103 143 246 (accept_3_4 103 143 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 143 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 102 143 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 143 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 143 246 (accept_3_4 100 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 143 246 (Polychromatic418967fa.accept_10_9_3_6_1_686 99 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 143 246 (Polychromatic418967fa.accept_10_8_3_6_1_685 98 143 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 143 246 (accept_3_4 97 143 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 143 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 96 143 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 143 246
  (Polychromatic418967fa.accept_7_4_3_1_1_87 95 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 143 246 (accept_3_4 94 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 143 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 143 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 92 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 143 246 (accept_3_4 91 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 143 246 (Polychromatic418967fa.accept_19_14_10_18_1_5244 90 143 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 143 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 143 246 (accept_3_4 88 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 143 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 87 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 143 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 86 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 143 246 (accept_3_4 85 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 143 246 (Polychromatic418967fa.accept_17_16_7_8_1_7638 84 143 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 143 246
  (Polychromatic418967fa.accept_9_2_8_3_1_181 83 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 143 246 (accept_3_4 82 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 143 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 143 246 (Polychromatic418967fa.accept_23_11_5_16_1_13291 80 143 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 143 246 (accept_3_4 79 143 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 143 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 78 143 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 143 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 143 246 (accept_3_4 76 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 143 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 143 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 74 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 143 246 (accept_3_4 73 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 143 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 143 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 143 246
  (Polychromatic418967fa.accept_16_7_15_6_1_1428 71 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 143 246 (accept_3_4 70 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 143 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 143 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 143 246 (accept_3_4 67 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 143 246 (Polychromatic418967fa.accept_19_9_10_18_1_10811 66 143 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 143 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 143 246 (accept_3_4 64 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 143 246 (Polychromatic418967fa.accept_18_9_17_12_1_462 63 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 143 246 (Polychromatic418967fa.accept_15_2_8_6_1_1340 62 143 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 143 246 (accept_3_4 61 143 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 143 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 143 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 143 246
  (Polychromatic418967fa.accept_9_5_8_3_1_437 59 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 143 246 (accept_3_4 58 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 143 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 143 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 56 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 143 246 (accept_3_4 55 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 143 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 143 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 143 246 (accept_3_4 52 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 143 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 143 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 50 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 143 246 (accept_3_4 49 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 143 246 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 143 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 143 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 143 246 (accept_3_4 46 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 143 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 143 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 143 246 (accept_3_4 43 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 143 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 143 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 143 246 (accept_3_4 40 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 143 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 143 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 38 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 246 (accept_3_4 37 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 246 (Polychromatic418967fa.accept_19_17_10_18_1_9563 36 143 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 246
  (Polychromatic418967fa.accept_17_1_7_8_1_6347 35 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 246 (accept_3_4 34 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 246 (accept_3_4 31 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 143 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 246 (accept_3_4 28 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 246 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 246 (accept_3_4 25 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 143 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 246
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 246 (accept_3_4 22 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 246 (accept_3_4 19 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 143 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 143 246 (accept_3_4 16 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 143 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 143 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 246 (accept_3_4 13 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 143 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 246
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 246 (accept_3_4 10 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 246 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 246 (accept_3_4 7 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 143 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 246 (accept_3_4 4 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 246 (Polychromatic418967fa.accept_21_3_17_15_1_4199 3 143 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 246 (accept_3_4 1 143 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 142 246 (Eq.refl Bool.true) (allA_succ_of_gcd 104 142 246 2 52 71 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 142 246
  (Polychromatic418967fa.accept_9_4_7_3_1_43 103 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 142 246 2 51 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 142 246 (accept_3_5 101 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 142 246 2 50 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 142 246 (Polychromatic418967fa.accept_12_3_10_6_1_442 99 142 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 142 246 2 49 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 142 246
  (Polychromatic418967fa.accept_7_6_2_1_1_214 97 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 142 246 2 48 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 142 246 (accept_3_5 95 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 142 246 2 47 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 142 246 (Polychromatic418967fa.accept_11_5_10_4_1_1157 93 142 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 142 246 2 46 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 142 246
  (Polychromatic418967fa.accept_9_1_7_3_1_41 91 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 142 246 2 45 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 142 246 (accept_3_5 89 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 142 246 2 44 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 142 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 142 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 142 246 2 43 71 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 142 246
  (Polychromatic418967fa.accept_9_4_7_3_1_43 85 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 142 246 2 42 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 142 246 (accept_3_5 83 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 142 246 2 41 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 142 246 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 142 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 142 246 2 40 71 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 142 246
  (Polychromatic418967fa.accept_19_3_9_18_1_10979 79 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 142 246 2 39 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 142 246 (accept_3_5 77 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 142 246 2 38 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 142 246 (Polychromatic418967fa.accept_12_3_10_6_1_442 75 142 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 142 246 2 37 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 142 246
  (Polychromatic418967fa.accept_7_3_2_1_1_225 73 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 142 246 2 36 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 142 246 (accept_3_5 71 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 142 246 2 35 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 142 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 142 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 142 246 2 34 71 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 142 246
  (Polychromatic418967fa.accept_9_4_7_3_1_43 67 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 142 246 2 33 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 142 246 (accept_3_5 65 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 142 246 2 32 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 142 246 (Polychromatic418967fa.accept_12_3_10_6_1_442 63 142 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 142 246 2 31 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 142 246
  (Polychromatic418967fa.accept_10_1_2_6_1_638 61 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 142 246 2 30 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 142 246 (accept_3_5 59 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 142 246 2 29 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 142 246 (Polychromatic418967fa.accept_12_9_10_6_1_872 57 142 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 142 246 2 28 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 142 246
  (Polychromatic418967fa.accept_7_6_2_1_1_214 55 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 142 246 2 27 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 142 246 (accept_3_5 53 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 142 246 2 26 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 142 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 142 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 142 246 2 25 71 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 142 246
  (Polychromatic418967fa.accept_9_4_7_3_1_43 49 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 142 246 2 24 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 142 246 (accept_3_5 47 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 142 246 2 23 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 142 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 142 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 142 246 2 22 71 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 142 246
  (Polychromatic418967fa.accept_14_1_2_8_1_655 43 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 142 246 2 21 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 142 246 (accept_3_5 41 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 142 246 2 20 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 142 246 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 142 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 142 246 2 19 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 246
  (Polychromatic418967fa.accept_9_1_7_3_1_41 37 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 142 246 2 18 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 142 246 (accept_3_5 35 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 246 2 17 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 142 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 246 2 16 71 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 246
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 246 2 15 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 246 (accept_3_5 29 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 246 2 14 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 142 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 246 2 13 71 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 246
  (Polychromatic418967fa.accept_19_6_9_18_1_8140 25 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 246 2 12 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 246 (accept_3_5 23 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 246 2 11 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 246 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 142 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 246 2 10 71 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 246
  (Polychromatic418967fa.accept_9_1_7_3_1_41 19 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 246 2 9 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 142 246 (accept_3_5 17 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 142 246 2 8 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 142 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 142 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 142 246 2 7 71 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 142 246
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 142 246 2 6 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 142 246 (accept_3_5 11 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 142 246 2 5 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 142 246 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 142 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 142 246 2 4 71 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 142 246
  (Polychromatic418967fa.accept_22_7_10_4_1_2290 7 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 142 246 2 3 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 142 246 (accept_3_5 5 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 142
  246 2 2 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  142 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 142 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 142 246 2 1 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 142 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 142 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 141 246 (Eq.refl Bool.true) (allA_succ_of_gcd 105 141 246 3 35 47 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 141 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 104 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 141 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 141 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 141 246 3 34 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 141 246 (Polychromatic418967fa.accept_9_2_6_3_1_178
  101 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 141 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 100 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 141 246 3 33 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 141 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 98 141 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 141 246 (Polychromatic418967fa.accept_9_7_6_3_1_456
  97 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 141 246 3 32 47 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 141 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 141 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 94 141 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 141 246 3 31 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 141 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 92
  141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 141 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 91 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 141 246 3 30 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 141 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 89 141 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 141 246 (Polychromatic418967fa.accept_9_7_6_3_1_456
  88 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 141 246 3 29 47 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 141 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 86 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 141 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 85 141 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 141 246 3 28 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 141 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 83
  141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 141 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 82 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 141 246 3 27 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 141 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 80 141 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 79
  141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 141 246 3 26 47 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 141 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 77 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 141 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 76 141 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 141 246 3 25 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 141 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 74
  141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 73 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 141 246 3 24 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 141 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 141 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 141 246 (Polychromatic418967fa.accept_9_7_6_3_1_456
  70 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 141 246 3 23 47 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 141 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 68 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 141 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 141 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 141 246 3 22 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 141 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 65
  141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 141 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 64 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 141 246 3 21 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 141 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 62 141 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 246 (Polychromatic418967fa.accept_9_7_6_3_1_456
  61 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 141 246 3 20 47 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 141 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 141 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 58 141 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 141 246 3 19 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 141 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 56
  141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 141 246 3 18 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 141 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 53 141 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 246 (Polychromatic418967fa.accept_9_7_6_3_1_456
  52 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 141 246 3 17 47 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 141 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 50 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 141 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 141 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 141 246 3 16 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 141 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 46 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 141 246 3 15 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 141 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 44 141 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 141 246 3 14 47 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 141 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 41 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 141 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 141 246 3 13 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 141 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 38
  141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 141 246 3 12 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 141 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 141 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 246 (Polychromatic418967fa.accept_9_7_6_3_1_456
  34 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 141 246 3 11 47 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 141 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 32 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 141 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 141 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 141 246 3 10 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 141 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 141 246 3 9 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 141 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 141 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 246 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 141 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 141 246 3 8 47 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 141 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 141 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 141 246 3 7 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 141 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 20
  141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 141 246 3 6 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 141 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 141 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 246 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 141 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 141 246 3 5 47 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 141 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 141 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 141 246 3 4 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 141 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 141 246 3 3 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 141 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 141 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 141 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 141 246 3 2 47 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 141 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 141 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 246 3 1 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 141 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 141 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 141
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 140 246 (Eq.refl Bool.true) (allA_succ_of_gcd 106 140 246 2 53 70 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 140 246
  (Polychromatic418967fa.accept_9_6_5_3_1_205 105 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 140 246 2 52 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 140 246 (accept_3_4 103 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 140 246 2 51 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 140 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 101 140 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 140 246 2 50 70 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 140 246
  (Polychromatic418967fa.accept_12_3_8_6_1_895 99 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 140 246 2 49 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 140 246 (accept_3_4 97 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 140 246 2 48 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 140 246 (Polychromatic418967fa.accept_11_7_8_4_1_718 95 140 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 140 246 2 47 70 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 140 246
  (Polychromatic418967fa.accept_12_9_8_6_1_466 93 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 140 246 2 46 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 140 246 (accept_3_4 91 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 140 246 2 45 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 140 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 89 140 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 140 246 2 44 70 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 140 246
  (Polychromatic418967fa.accept_9_6_5_3_1_205 87 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 140 246 2 43 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 140 246 (accept_3_4 85 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 140 246 2 42 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 140 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 83 140 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 140 246 2 41 70 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 140 246
  (Polychromatic418967fa.accept_12_9_8_6_1_466 81 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 140 246 2 40 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 140 246 (accept_3_4 79 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 140 246 2 39 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 140 246 (Polychromatic418967fa.accept_19_1_7_18_1_10869 77 140 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 140 246 2 38 70 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 140 246
  (Polychromatic418967fa.accept_12_3_8_6_1_895 75 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 140 246 2 37 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 140 246 (accept_3_4 73 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 140 246 2 36 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 140 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 71 140 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 140 246 2 35 70 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 140 246
  (Polychromatic418967fa.accept_9_6_5_3_1_205 69 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 140 246 2 34 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 140 246 (accept_3_4 67 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 140 246 2 33 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 140 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 65 140 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 140 246 2 32 70 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 140 246
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 140 246 2 31 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 140 246 (accept_3_4 61 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 140 246 2 30 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 140 246 (Polychromatic418967fa.accept_13_7_10_12_1_2047 59 140 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 140 246 2 29 70 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 140 246
  (Polychromatic418967fa.accept_12_9_8_6_1_466 57 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 140 246 2 28 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 140 246 (accept_3_4 55 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 140 246 2 27 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 140 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 53 140 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 140 246 2 26 70 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 140 246
  (Polychromatic418967fa.accept_9_6_5_3_1_205 51 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 140 246 2 25 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 140 246 (accept_3_4 49 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 140 246 2 24 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 140 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 47 140 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 140 246 2 23 70 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 140 246
  (Polychromatic418967fa.accept_11_1_8_4_1_717 45 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 140 246 2 22 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 140 246 (accept_3_4 43 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 140 246 2 21 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 140 246 (Polychromatic418967fa.accept_13_2_10_12_1_757 41 140 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 246 2 20 70 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 246
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 140 246 2 19 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 140 246 (accept_3_4 37 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 140 246 2 18 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 140 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 140 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 140 246 2 17 70 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 246
  (Polychromatic418967fa.accept_9_6_5_3_1_205 33 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 140 246 2 16 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 140 246 (accept_3_4 31 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 140 246 2 15 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 140 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 140 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 246 2 14 70 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 246
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 140 246 2 13 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 140 246 (accept_3_4 25 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 140 246 2 12 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 140 246 (Polychromatic418967fa.accept_11_1_8_4_1_717 23 140 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 246 2 11 70 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 246
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 140 246 2 10 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 140 246 (accept_3_4 19 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 140 246 2 9 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 140 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 140 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 246 2 8 70 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 140 246
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 140 246 2 7 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 140 246 (accept_3_4 13 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 140 246 2 6 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 140 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 140 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 246 2 5 70 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 246
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 140 246 2 4 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 140 246 (accept_3_4 7 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140
  246 2 3 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  140 246 (Polychromatic418967fa.accept_21_5_14_15_1_7290 5 140 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 140 246 2 2 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 140 246 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 140 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 246 2 1 70 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 246 (accept_3_4 1 140 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 139 246 (Eq.refl Bool.true) (allA_succ_of_accept 107 139 246 (accept_3_5 107 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 139 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 106 139
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 139 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 105 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 139 246 (accept_3_5 104 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 139 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 103 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 139 246 (Polychromatic418967fa.accept_11_3_7_4_1_1133 102 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 139 246 (accept_3_5 101 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 139 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 100 139
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 139 246
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 99 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 139 246 (accept_3_5 98 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 139 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 139 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 96 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 139 246 (accept_3_5 95 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 139 246 (Polychromatic418967fa.accept_13_3_9_12_1_2062 94 139 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 139 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 139 246 (accept_3_5 92 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 139 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 91 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 139 246 (Polychromatic418967fa.accept_17_5_3_8_1_1697 90 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 139 246 (accept_3_5 89 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 139 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 88 139 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 139 246
  (Polychromatic418967fa.accept_9_6_4_3_1_203 87 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 139 246 (accept_3_5 86 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 139 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 139 246 (Polychromatic418967fa.accept_15_9_4_6_1_3075 84 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 139 246 (accept_3_5 83 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 139 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 82 139 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 139 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 139 246 (accept_3_5 80 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 139 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 79 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 139 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 78 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 139 246 (accept_3_5 77 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 139 246 (Polychromatic418967fa.accept_22_10_7_4_1_7008 76 139 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 139 246
  (Polychromatic418967fa.accept_7_5_6_1_1_407 75 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 139 246 (accept_3_5 74 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 139 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 139 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 139 246 (accept_3_5 71 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 139 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 139 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 139 246 (accept_3_5 68 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 139 246 (Polychromatic418967fa.accept_16_3_11_6_1_4467 67 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 139 246 (Polychromatic418967fa.accept_16_2_11_6_1_737 66 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 139 246 (accept_3_5 65 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 139 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 64 139 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 139 246
  (Polychromatic418967fa.accept_10_3_9_6_1_94 63 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 139 246 (accept_3_5 62 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 139 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 139 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 60 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 139 246 (accept_3_5 59 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 139 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 139 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 139 246 (accept_3_5 56 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 139 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 55 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 139 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 139 246 (accept_3_5 53 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 139 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 139 246
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 139 246 (accept_3_5 50 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 139 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 139 246 (Polychromatic418967fa.accept_21_6_13_15_1_11870 48 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 246 (accept_3_5 47 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 139 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 246 (accept_3_5 44 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 246 (accept_3_5 41 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 246
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 39 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 246 (accept_3_5 38 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 246 (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 246 (accept_3_5 35 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 139 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 246 (accept_3_5 32 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 246 (Polychromatic418967fa.accept_19_12_6_18_1_8095 31 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 246 (accept_3_5 29 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 246
  (Polychromatic418967fa.accept_20_7_19_6_1_4742 27 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 246 (accept_3_5 26 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 246 (accept_3_5 23 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 246 (Polychromatic418967fa.accept_17_5_3_8_1_1697 22 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 246 (accept_3_5 20 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 246 (Polychromatic418967fa.accept_16_2_11_6_1_737 18 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 246 (accept_3_5 17 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 139 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 246
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 246 (accept_3_5 14 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 246 (accept_3_5 11 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 246 (accept_3_5 8 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 246 (accept_3_5 5 139 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 246 (Polychromatic418967fa.accept_16_4_11_6_1_5591 4 139 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 246
  (Polychromatic418967fa.accept_10_3_9_6_1_94 3 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 246 (accept_3_5 2 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 139 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 138 246 (Eq.refl Bool.true) (allA_succ_of_gcd 108 138 246 6 18 23 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 138 246
  (Polychromatic418967fa.accept_24_11_18_6_1_11499 107 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 138 246 2 53 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 105 138 246 3 35 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 138 246 2 52 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 138 246 (Polychromatic418967fa.accept_10_3_8_6_1_326
  103 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 138 246 6 17 23 41
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 138 246
  (Polychromatic418967fa.accept_7_3_5_1_1_72 101 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 138 246 2 50 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 99 138 246 3 33 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 138 246 2 49 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 138 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 97 138 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 138 246 6 16 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 138 246
  (Polychromatic418967fa.accept_7_4_5_1_1_418 95 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 138 246 2 47 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 93 138 246 3 31 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 138 246 2 46 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 138 246 (Polychromatic418967fa.accept_15_1_3_6_1_621 91 138 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 138 246 6 15 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 138 246
  (Polychromatic418967fa.accept_19_13_5_18_1_8106 89 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 138 246 2 44 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 87 138 246 3 29 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 138 246 2 43 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 138 246 (Polychromatic418967fa.accept_13_7_8_12_1_2810
  85 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 138 246 6 14 23 41
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 138 246
  (Polychromatic418967fa.accept_7_6_5_1_1_416 83 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 138 246 2 41 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 138 246 3 27 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 138 246 2 40 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 138 246 (Polychromatic418967fa.accept_11_2_6_4_1_3028 79 138
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 138 246 6 13 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 138 246
  (Polychromatic418967fa.accept_19_1_5_18_1_8109 77 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 138 246 2 38 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 138 246 3 25 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 138 246 2 37 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 138 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 73 138 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 138 246 6 12 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 138 246
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 71 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 138 246 2 35 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 138 246 3 23 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 138 246 2 34 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 138 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 138 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 138 246 6 11 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 138 246
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 65 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 138 246 2 32 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 138 246 3 21 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 138 246 2 31 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 138 246 (Polychromatic418967fa.accept_13_9_8_12_1_2031 61 138
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 138 246 6 10 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 138 246
  (Polychromatic418967fa.accept_7_3_5_1_1_72 59 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 138 246 2 29 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 138 246 3 19 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 138 246 2 28 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 138 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 138 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 138 246 6 9 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 138 246
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 138 246 2 26 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 138 246 3 17 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 138 246 2 25 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 246 (Polychromatic418967fa.accept_13_10_8_12_1_2032 49 138
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 138 246 6 8 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 138 246
  (Polychromatic418967fa.accept_19_9_5_18_1_3891 47 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 138 246 2 23 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 138 246 3 15 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 138 246 2 22 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 246 (Polychromatic418967fa.accept_10_3_8_6_1_326 43 138 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 138 246 6 7 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 138 246
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 138 246 2 20 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 138 246 3 13 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 138 246 2 19 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 246 (Polychromatic418967fa.accept_24_13_18_6_1_6209 37 138
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 138 246 6 6 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 138 246
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 138 246 2 17 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 138 246 3 11 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 138 246 2 16 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 138 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 138 246 6 5 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 138 246
  (Polychromatic418967fa.accept_19_10_5_18_1_10817 29 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 138 246 2 14 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 27 138 246 3 9 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 26 138 246 2 13 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 138 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 138 246 6 4 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 138 246
  (Polychromatic418967fa.accept_10_3_8_6_1_326 23 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 138 246 2 11 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 138 246 3 7 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 138 246 2 10 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 138 246 (Polychromatic418967fa.accept_21_19_12_15_1_7307 19 138 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 138 246 6 3 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 138 246
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 138 246 2 8 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 138 246 3 5 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 138 246 2 7 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 138 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 138 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 246 6 2 23 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 246
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 246 2 5 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 138 246 3 3 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 138 246 2 4 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 138 246 (Polychromatic418967fa.accept_13_7_8_12_1_2810 7 138 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 246 6 1 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 246 (Polychromatic418967fa.accept_13_5_8_12_1_2759
  5 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138 246 2 2 69 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 138 246 3 1 46 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 138 246 2 1 69 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 246
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 1 138 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 138
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 137 246 (Eq.refl Bool.true) (allA_succ_of_accept 109 137 246 (accept_3_4 109 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 137 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 108 137
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 137 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 107 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 137 246 (accept_3_4 106 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 137 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 105 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 137 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 104 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 137 246 (accept_3_4 103 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 137 246 (Polychromatic418967fa.accept_13_11_7_12_1_2758 102
  137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 137 246
  (Polychromatic418967fa.accept_7_3_4_1_1_71 101 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 137 246 (accept_3_4 100 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 137 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 137 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 98 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 137 246 (accept_3_4 97 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 137 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 96 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 137 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 137 246 (accept_3_4 94 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 137 246 (Polychromatic418967fa.accept_10_3_7_6_1_659 93 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 137 246 (Polychromatic418967fa.accept_17_7_1_8_1_6280 92 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 137 246 (accept_3_4 91 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 137 246 (Polychromatic418967fa.accept_19_14_4_18_1_6665 90 137
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 137 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 89 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 137 246 (accept_3_4 88 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 137 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 137 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 86 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 137 246 (accept_3_4 85 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 137 246 (Polychromatic418967fa.accept_13_6_7_12_1_3504 84 137 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 137 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 137 246 (accept_3_4 82 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 137 246 (Polychromatic418967fa.accept_10_1_7_6_1_91 81 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 137 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 80 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 137 246 (accept_3_4 79 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 137 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 78 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 137 246
  (Polychromatic418967fa.accept_9_5_2_3_1_194 77 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 137 246 (accept_3_4 76 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 137 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 137 246 (Polychromatic418967fa.accept_14_4_11_8_1_2034 74 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 137 246 (accept_3_4 73 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 137 246 (Polychromatic418967fa.accept_15_12_2_6_1_2127 72 137
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 137 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 137 246 (accept_3_4 70 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 137 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 137 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 68 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 137 246 (accept_3_4 67 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 137 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 137 246
  (Polychromatic418967fa.accept_11_10_5_4_1_711 65 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 137 246 (accept_3_4 64 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 137 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 137 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 62 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 137 246 (accept_3_4 61 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 137 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 137 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 137 246 (accept_3_4 58 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 137 246 (Polychromatic418967fa.accept_13_5_7_12_1_2757 57 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 137 246 (Polychromatic418967fa.accept_13_4_7_12_1_2823 56 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 137 246 (accept_3_4 55 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 137 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 137 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 137 246
  (Polychromatic418967fa.accept_9_8_2_3_1_447 53 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 137 246 (accept_3_4 52 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 137 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 137 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 50 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 246 (accept_3_4 49 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 246 (Polychromatic418967fa.accept_21_6_11_15_1_13454 48 137 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 137 246 (accept_3_4 46 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 137 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 137 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 44 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 246 (accept_3_4 43 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 246
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 137 246 (accept_3_4 40 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 137 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 137 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 246 (accept_3_4 37 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 246 (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 137 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 137 246 (accept_3_4 34 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 137 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 137 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 32 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 246 (accept_3_4 31 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 246 (Polychromatic418967fa.accept_13_4_7_12_1_2823 30 137 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 246
  (Polychromatic418967fa.accept_16_13_9_6_1_2306 29 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 137 246 (accept_3_4 28 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 137 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 137 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 246 (accept_3_4 25 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 137 246 (accept_3_4 22 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 137 246 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 137 246 (Polychromatic418967fa.accept_26_20_7_12_1_14805 20 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 246 (accept_3_4 19 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 246 (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 137
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 246
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 137 246 (accept_3_4 16 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 137 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 137 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 246 (accept_3_4 13 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 137 246 (accept_3_4 10 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  137 246 (Polychromatic418967fa.accept_17_9_1_8_1_5045 9 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 137 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 246 (accept_3_4 7 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 137 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 246 (accept_3_4 4 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 137 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 246 (Polychromatic418967fa.accept_16_2_9_6_1_4441 2 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 246 (accept_3_4 1 137 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 137
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 111 136 246 (Eq.refl Bool.true) (allA_succ_of_gcd 110 136 246 2 55 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 136 246
  (Polychromatic418967fa.accept_7_4_3_1_1_87 109 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 136 246 2 54 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 136 246 (accept_3_5 107 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 136 246 2 53 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 136 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 105 136 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 136 246 2 52 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 136 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 103 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 136 246 2 51 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 136 246 (accept_3_5 101 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 136 246 2 50 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 136 246 (Polychromatic418967fa.accept_12_3_4_6_1_434 99 136 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 136 246 2 49 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 136 246
  (Polychromatic418967fa.accept_9_7_1_3_1_443 97 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 136 246 2 48 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 136 246 (accept_3_5 95 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 136 246 2 47 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 136 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 93 136 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 136 246 2 46 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 136 246
  (Polychromatic418967fa.accept_19_15_3_18_1_5241 91 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 136 246 2 45 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 136 246 (accept_3_5 89 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 136 246 2 44 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 136 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 87 136 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 136 246 2 43 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 136 246
  (Polychromatic418967fa.accept_9_4_1_3_1_190 85 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 136 246 2 42 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 136 246 (accept_3_5 83 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 136 246 2 41 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 136 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 136 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 136 246 2 40 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 136 246
  (Polychromatic418967fa.accept_7_2_3_1_1_10 79 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 136 246 2 39 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 136 246 (accept_3_5 77 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 136 246 2 38 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 136 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 136 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 136 246 2 37 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 136 246
  (Polychromatic418967fa.accept_19_16_3_18_1_8120 73 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 136 246 2 36 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 136 246 (accept_3_5 71 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 136 246 2 35 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 136 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 69 136 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 136 246 2 34 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 136 246
  (Polychromatic418967fa.accept_7_4_3_1_1_87 67 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 136 246 2 33 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 136 246 (accept_3_5 65 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 136 246 2 32 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 136 246 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 136 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 136 246 2 31 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 136 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 61 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 136 246 2 30 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 136 246 (accept_3_5 59 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 136 246 2 29 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 136 246 (Polychromatic418967fa.accept_12_9_4_6_1_460 57 136 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 136 246 2 28 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 136 246
  (Polychromatic418967fa.accept_15_10_1_6_1_3033 55 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 136 246 2 27 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 136 246 (accept_3_5 53 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 136 246 2 26 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 136 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 136 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 136 246 2 25 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 136 246
  (Polychromatic418967fa.accept_9_4_1_3_1_190 49 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 136 246 2 24 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 136 246 (accept_3_5 47 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 136 246 2 23 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 136 246 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 136 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 136 246 2 22 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 136 246
  (Polychromatic418967fa.accept_9_7_1_3_1_443 43 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 136 246 2 21 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 136 246 (accept_3_5 41 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 136 246 2 20 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 136 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 136 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 136 246 2 19 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 136 246
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 136 246 2 18 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 136 246 (accept_3_5 35 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 136 246 2 17 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 136 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 136 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 136 246 2 16 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 136 246
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 136 246 2 15 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 136 246 (accept_3_5 29 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 136 246 2 14 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 136 246 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 136 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 136 246 2 13 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 246
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 136 246 2 12 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 136 246 (accept_3_5 23 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 136 246 2 11 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 136 246 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 136 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 246 2 10 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 136 246 2 9 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 136 246 (accept_3_5 17 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 136 246 2 8 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 136 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 136 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 136 246 2 7 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 136 246
  (Polychromatic418967fa.accept_9_4_1_3_1_190 13 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 136 246 2 6 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 136 246 (accept_3_5 11 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 136 246 2 5 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 136 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 136 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 136 246 2 4 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 136 246
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 136 246 2 3 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 136 246 (accept_3_5 5 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136
  246 2 2 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  136 246 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 136 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 136 246 2 1 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 136 246 (Polychromatic418967fa.accept_20_1_16_6_1_4715 1 136 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 135 246 (Eq.refl Bool.true) (allA_succ_of_gcd 111 135 246 3 37 45 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 135 246
  (Polychromatic418967fa.accept_12_2_3_6_1_112 110 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 135 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 135 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 135 246 3 36 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 135 246
  (Polychromatic418967fa.accept_18_17_9_12_1_2160 107 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 135 246 (Polychromatic418967fa.accept_11_7_3_4_1_729 106 135 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 135 246 3 35 45 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 135 246
  (Polychromatic418967fa.accept_7_6_2_1_1_214 104 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 135 246 (Polychromatic418967fa.accept_21_19_9_15_1_4217 103 135 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 135 246 3 34 45 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 135 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 135 246 (Polychromatic418967fa.accept_12_4_3_6_1_879 100 135 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 135 246 3 33 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 135 246 (Polychromatic418967fa.accept_12_2_3_6_1_112
  98 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 135 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 97 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 135 246 3 32 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 135 246 (Polychromatic418967fa.accept_11_7_3_4_1_729 95 135 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 135 246 (Polychromatic418967fa.accept_7_3_2_1_1_225
  94 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 135 246 3 31 45 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 135 246
  (Polychromatic418967fa.accept_12_8_3_6_1_909 92 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 135 246 (Polychromatic418967fa.accept_10_1_5_6_1_649 91 135 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 135 246 3 30 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 135 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 89
  135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 135 246
  (Polychromatic418967fa.accept_12_4_3_6_1_879 88 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 135 246 3 29 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 135 246 (Polychromatic418967fa.accept_12_2_3_6_1_112 86 135 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 135 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 85
  135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 135 246 3 28 45 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 135 246
  (Polychromatic418967fa.accept_7_6_2_1_1_214 83 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 135 246 (Polychromatic418967fa.accept_12_10_3_6_1_882 82 135 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 135 246 3 27 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 135 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 80
  135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 135 246
  (Polychromatic418967fa.accept_10_9_5_6_1_691 79 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 135 246 3 26 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 135 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 135 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 246 (Polychromatic418967fa.accept_7_6_2_1_1_214
  76 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 135 246 3 25 45 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 135 246
  (Polychromatic418967fa.accept_10_4_5_6_1_651 74 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 135 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 135 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 135 246 3 24 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 135 246 (Polychromatic418967fa.accept_10_1_5_6_1_649
  71 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 246
  (Polychromatic418967fa.accept_12_10_3_6_1_882 70 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 135 246 3 23 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 135 246 (Polychromatic418967fa.accept_12_8_3_6_1_909 68 135 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 246
  (Polychromatic418967fa.accept_13_2_5_12_1_2043 67 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 135 246 3 22 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 135 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 135 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 135 246 (Polychromatic418967fa.accept_10_4_5_6_1_651
  64 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 135 246 3 21 45 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 135 246
  (Polychromatic418967fa.accept_7_6_2_1_1_214 62 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 135 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 135 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 135 246 3 20 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 135 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 59
  135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 246
  (Polychromatic418967fa.accept_12_10_3_6_1_882 58 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 135 246 3 19 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 135 246 (Polychromatic418967fa.accept_12_8_3_6_1_909 56 135 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 246 (Polychromatic418967fa.accept_7_6_2_1_1_214
  55 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 135 246 3 18 45 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 135 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 135 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 135 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 135 246 3 17 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 135 246 (Polychromatic418967fa.accept_12_2_3_6_1_112
  50 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 135 246 3 16 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 135 246 (Polychromatic418967fa.accept_13_8_5_12_1_2755 47 135 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 246
  (Polychromatic418967fa.accept_12_10_3_6_1_882 46 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 135 246 3 15 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 135 246 (Polychromatic418967fa.accept_10_4_5_6_1_651 44 135 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 246 (Polychromatic418967fa.accept_13_4_5_12_1_751
  43 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 135 246 3 14 45 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 135 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 135 246 (Polychromatic418967fa.accept_11_7_3_4_1_729 40 135 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 135 246 3 13 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 135 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 38
  135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 135 246 3 12 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 135 246 (Polychromatic418967fa.accept_18_17_9_12_1_2160 35 135 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 246
  (Polychromatic418967fa.accept_7_6_2_1_1_214 34 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 135 246 3 11 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 135 246 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 135 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 246 (Polychromatic418967fa.accept_7_3_2_1_1_225
  31 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 135 246 3 10 45 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 135 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 246 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 135 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 135 246 3 9 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 135 246 (Polychromatic418967fa.accept_12_2_3_6_1_112
  26 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 135 246 3 8 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 135 246 (Polychromatic418967fa.accept_18_5_9_12_1_8461 23 135 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 246 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 135
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 135 246 3 7 45 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 135 246
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 246 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 135 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 135 246 3 6 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 135 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 246
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 135 246 3 5 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 135 246 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 135 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 135 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 246 3 4 45 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 246
  (Polychromatic418967fa.accept_10_1_5_6_1_649 11 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 135 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 135 246 3 3 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 135 246 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 135 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 246
  (Polychromatic418967fa.accept_11_7_3_4_1_729 7 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 135 246 3 2 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 135 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 135 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 246 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 135 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 135 246 3 1 45 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 135 246
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 135 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 135 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 135
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 134 246 (Eq.refl Bool.true) (allA_succ_of_gcd 112 134 246 2 56 67 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 134 246
  (Polychromatic418967fa.accept_12_3_2_6_1_138 111 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 134 246 2 55 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 134 246 (accept_3_4 109 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 134 246 2 54 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 134 246 (Polychromatic418967fa.accept_13_3_4_12_1_36 107 134 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 134 246 2 53 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 134 246
  (Polychromatic418967fa.accept_9_6_8_3_1_183 105 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 134 246 2 52 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 134 246 (accept_3_4 103 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 134 246 2 51 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 134 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 101 134 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 134 246 2 50 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 134 246
  (Polychromatic418967fa.accept_12_3_2_6_1_138 99 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 134 246 2 49 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 134 246 (accept_3_4 97 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 134 246 2 48 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 134 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 95 134 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 134 246 2 47 67 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 134 246
  (Polychromatic418967fa.accept_12_9_2_6_1_455 93 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 134 246 2 46 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 134 246 (accept_3_4 91 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 134 246 2 45 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 134 246 (Polychromatic418967fa.accept_13_11_4_12_1_3585 89 134 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 134 246 2 44 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 134 246
  (Polychromatic418967fa.accept_9_6_8_3_1_183 87 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 134 246 2 43 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 134 246 (accept_3_4 85 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 134 246 2 42 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 134 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 83 134 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 134 246 2 41 67 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 134 246
  (Polychromatic418967fa.accept_12_9_2_6_1_455 81 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 134 246 2 40 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 134 246 (accept_3_4 79 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 134 246 2 39 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 134 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 77 134 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 134 246 2 38 67 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 134 246
  (Polychromatic418967fa.accept_10_5_4_6_1_319 75 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 134 246 2 37 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 134 246 (accept_3_4 73 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 134 246 2 36 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 134 246 (Polychromatic418967fa.accept_19_14_1_18_1_5280 71 134 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 134 246 2 35 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 134 246
  (Polychromatic418967fa.accept_9_6_8_3_1_183 69 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 134 246 2 34 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 134 246 (accept_3_4 67 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 134 246 2 33 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 134 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 65 134 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 134 246 2 32 67 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 134 246
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 134 246 2 31 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 134 246 (accept_3_4 61 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 134 246 2 30 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 134 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 59 134 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 134 246 2 29 67 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 134 246
  (Polychromatic418967fa.accept_12_9_2_6_1_455 57 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 134 246 2 28 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 134 246 (accept_3_4 55 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 134 246 2 27 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 134 246 (Polychromatic418967fa.accept_11_9_2_4_1_707 53 134 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 134 246 2 26 67 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 246
  (Polychromatic418967fa.accept_9_6_8_3_1_183 51 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 134 246 2 25 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 134 246 (accept_3_4 49 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 134 246 2 24 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 134 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 134 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 134 246 2 23 67 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 246
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 134 246 2 22 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 134 246 (accept_3_4 43 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 134 246 2 21 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 134 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 134 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 246 2 20 67 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 246
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 246 2 19 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 246 (accept_3_4 37 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 246 2 18 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 246 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 134 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 246 2 17 67 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 246
  (Polychromatic418967fa.accept_9_6_8_3_1_183 33 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 246 2 16 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 246 (accept_3_4 31 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 246 2 15 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 134 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 246 2 14 67 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 246
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 246 2 13 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 246 (accept_3_4 25 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 246 2 12 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 134 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 246 2 11 67 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 246
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 246 2 10 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 246 (accept_3_4 19 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 246 2 9 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 134 246 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 134 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 246 2 8 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 246
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 134 246 2 7 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 134 246 (accept_3_4 13 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 134 246 2 6 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 134 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 134 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 134 246 2 5 67 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 134 246
  (Polychromatic418967fa.accept_11_9_2_4_1_707 9 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 134 246 2 4 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 246 (accept_3_4 7 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134
  246 2 3 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  134 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 134 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 134 246 2 2 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 134 246 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 134 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 246 2 1 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 246 (accept_3_4 1 134 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 114 133 246 (Eq.refl Bool.true) (allA_succ_of_accept 113 133 246 (accept_3_5 113 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 133 246 (Polychromatic418967fa.accept_9_4_7_3_1_43 112 133
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 133 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 111 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 133 246 (accept_3_5 110 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 133 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 109 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 133 246 (Polychromatic418967fa.accept_10_8_3_6_1_685 108 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 133 246 (accept_3_5 107 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 133 246 (Polychromatic418967fa.accept_13_2_3_12_1_735 106 133
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 133 246
  (Polychromatic418967fa.accept_9_6_7_3_1_436 105 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 133 246 (accept_3_5 104 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 133 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 133 246 (Polychromatic418967fa.accept_21_18_7_15_1_2877 102 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 133 246 (accept_3_5 101 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 133 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 100 133
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 133 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 133 246 (accept_3_5 98 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 133 246 (Polychromatic418967fa.accept_10_7_3_6_1_644 97 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 133 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 96 133 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 133 246 (accept_3_5 95 133 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 133 246 (Polychromatic418967fa.accept_9_4_7_3_1_43 94 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 133 246
  (Polychromatic418967fa.accept_13_2_3_12_1_735 93 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 133 246 (accept_3_5 92 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 133 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 133 246 (Polychromatic418967fa.accept_14_6_7_8_1_624 90 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 133 246 (accept_3_5 89 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 133 246 (Polychromatic418967fa.accept_10_8_3_6_1_685 88 133
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 133 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 133 246 (accept_3_5 86 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 133 246 (Polychromatic418967fa.accept_9_4_7_3_1_43 85 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 133 246 (Polychromatic418967fa.accept_16_4_5_6_1_8071 84 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 133 246 (accept_3_5 83 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 133 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 82 133 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 133 246
  (Polychromatic418967fa.accept_16_1_5_6_1_4435 81 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 133 246 (accept_3_5 80 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 133 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 133 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 78 133 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 133 246 (accept_3_5 77 133 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 133 246 (Polychromatic418967fa.accept_9_4_7_3_1_43 76 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 133 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 133 246 (accept_3_5 74 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 133 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 73 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 133 246 (Polychromatic418967fa.accept_21_9_7_15_1_5769 72 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 133 246 (accept_3_5 71 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 133 246 (Polychromatic418967fa.accept_24_22_13_6_1_9818 70 133
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 133 246
  (Polychromatic418967fa.accept_9_6_7_3_1_436 69 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 133 246 (accept_3_5 68 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 133 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 133 246 (Polychromatic418967fa.accept_21_3_7_15_1_4300 66 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 246 (accept_3_5 65 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 133 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 64 133 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 133 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 133 246 (accept_3_5 62 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 133 246 (Polychromatic418967fa.accept_13_9_3_12_1_2025 61 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 133 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 60 133 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 246 (accept_3_5 59 133 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 246 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 133 246
  (Polychromatic418967fa.accept_10_7_3_6_1_644 57 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 133 246 (accept_3_5 56 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 133 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 133 246 (Polychromatic418967fa.accept_13_2_3_12_1_735 54 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 133 246 (accept_3_5 53 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 133 246 (Polychromatic418967fa.accept_11_8_1_4_1_2318 52 133
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 133 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 133 246 (accept_3_5 50 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 133 246 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 133 246 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 246 (accept_3_5 47 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 133 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 246
  (Polychromatic418967fa.accept_17_11_14_8_1_2729 45 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 133 246 (accept_3_5 44 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 133 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 133 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 133 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 133 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 246 (accept_3_5 41 133 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 246 (Polychromatic418967fa.accept_9_4_7_3_1_43 40
  133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 246 (accept_3_5 38 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 246 (Polychromatic418967fa.accept_16_4_5_6_1_8071 36 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 246 (accept_3_5 35 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 246 (Polychromatic418967fa.accept_14_6_7_8_1_624 34 133
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 246
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 246 (accept_3_5 32 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 246 (Polychromatic418967fa.accept_11_8_1_4_1_2318 30 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 246 (accept_3_5 29 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 133 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 246 (accept_3_5 26 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 246 (Polychromatic418967fa.accept_22_3_1_4_1_10270 25 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 133 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 246 (accept_3_5 23 133 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 246 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 246
  (Polychromatic418967fa.accept_18_3_7_12_1_1196 21 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 246 (accept_3_5 20 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 246 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 246 (accept_3_5 17 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 246 (Polychromatic418967fa.accept_17_16_14_8_1_7608 16 133
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 246 (accept_3_5 14 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 246 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 246 (Polychromatic418967fa.accept_21_12_7_15_1_7272 12 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 246 (accept_3_5 11 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 133 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 246
  (Polychromatic418967fa.accept_10_9_3_6_1_686 9 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 246 (accept_3_5 8 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 133 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 246 (accept_3_5 5 133 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 246 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 133 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 246 (accept_3_5 2 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 133 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 115 132 246 (Eq.refl Bool.true) (allA_succ_of_gcd 114 132 246 6 19 22 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 132 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 113 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 132 246 2 56 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 111 132 246 3 37 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 110 132 246 2 55 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 132 246 (Polychromatic418967fa.accept_9_1_6_3_1_177 109 132
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 132 246 6 18 22 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 132 246
  (Polychromatic418967fa.accept_7_2_6_1_1_73 107 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 132 246 2 53 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 132 246 3 35 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 132 246 2 52 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 132 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 103 132
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 132 246 6 17 22 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 132 246
  (Polychromatic418967fa.accept_9_2_6_3_1_178 101 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 132 246 2 50 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 99 132 246 3 33 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 132 246 2 49 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 132 246 (Polychromatic418967fa.accept_9_7_6_3_1_456 97 132 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 132 246 6 16 22 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 132 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 95 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 132 246 2 47 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 93 132 246 3 31 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 132 246 2 46 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 132 246 (Polychromatic418967fa.accept_9_1_6_3_1_177 91 132 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 132 246 6 15 22 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 132 246
  (Polychromatic418967fa.accept_7_5_6_1_1_407 89 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 132 246 2 44 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 87 132 246 3 29 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 132 246 2 43 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 132 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 85 132 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 132 246 6 14 22 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 132 246
  (Polychromatic418967fa.accept_9_2_6_3_1_178 83 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 132 246 2 41 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 132 246 3 27 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 132 246 2 40 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 132 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 79 132 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 132 246 6 13 22 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 132 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 77 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 132 246 2 38 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 132 246 3 25 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 132 246 2 37 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 132 246 (Polychromatic418967fa.accept_9_1_6_3_1_177 73 132 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 132 246 6 12 22 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 132 246
  (Polychromatic418967fa.accept_9_8_6_3_1_457 71 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 132 246 2 35 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 132 246 3 23 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 132 246 2 34 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 132 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 67 132 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 132 246 6 11 22 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 132 246
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 132 246 2 32 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 132 246 3 21 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 132 246 2 31 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 132 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 132 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 132 246 6 10 22 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 132 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 59 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 132 246 2 29 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 132 246 3 19 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 132 246 2 28 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 132 246 (Polychromatic418967fa.accept_9_1_6_3_1_177 55 132 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 132 246 6 9 22 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 132 246
  (Polychromatic418967fa.accept_9_8_6_3_1_457 53 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 132 246 2 26 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 132 246 3 17 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 132 246 2 25 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 132 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 132 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 132 246 6 8 22 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 132 246
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 132 246 2 23 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 132 246 3 15 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 132 246 2 22 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 246 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 132 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 132 246 6 7 22 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 132 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 41 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 132 246 2 20 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 132 246 3 13 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 132 246 2 19 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 132 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 132 246 6 6 22 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 132 246
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 132 246 2 17 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 132 246 3 11 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 132 246 2 16 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 132 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 246 6 5 22 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 246
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 246 2 14 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 132 246 3 9 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 132 246 2 13 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 132 246 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 132 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 246 6 4 22 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 246
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 132 246 2 11 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 132 246 3 7 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 132 246 2 10 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 132 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 132 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 246 6 3 22 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 246
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 132 246 2 8 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 132 246 3 5 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 132 246 2 7 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 132 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 132 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 246 6 2 22 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 246
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 132 246 2 5 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 132 246 3 3 44 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 132 246 2 4 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 132 246 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 132 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 246 6 1 22 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 5
  132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 246 2 2 66 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 132 246 3 1 44 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 132 246 2 1 66 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 132 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 132
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 131 246 (Eq.refl Bool.true) (allA_succ_of_accept 115 131 246 (accept_3_4 115 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 131 246 (Polychromatic418967fa.accept_9_6_5_3_1_205 114 131
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 131 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 113 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 131 246 (accept_3_4 112 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 131 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 111 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 131 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 110 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 131 246 (accept_3_4 109 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 131 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 108 131
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 131 246
  (Polychromatic418967fa.accept_9_8_5_3_1_777 107 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 131 246 (accept_3_4 106 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 131 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 131 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 104 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 131 246 (accept_3_4 103 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 131 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 102 131
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 131 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 131 246 (accept_3_4 100 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 131 246 (Polychromatic418967fa.accept_13_8_1_12_1_762 99 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 131 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 98 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 131 246 (accept_3_4 97 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 131 246 (Polychromatic418967fa.accept_9_6_5_3_1_205 96 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 131 246
  (Polychromatic418967fa.accept_7_4_5_1_1_418 95 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 131 246 (accept_3_4 94 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 131 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 131 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 92 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 131 246 (accept_3_4 91 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 131 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 90 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 131 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 131 246 (accept_3_4 88 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 131 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 131 246 (Polychromatic418967fa.accept_13_8_1_12_1_762 86 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 131 246 (accept_3_4 85 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 131 246 (Polychromatic418967fa.accept_15_9_11_6_1_637 84 131
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 131 246
  (Polychromatic418967fa.accept_7_6_5_1_1_416 83 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 131 246 (accept_3_4 82 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 131 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 131 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 80 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 131 246 (accept_3_4 79 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 131 246 (Polychromatic418967fa.accept_9_6_5_3_1_205 78 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 131 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 131 246 (accept_3_4 76 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 131 246 (Polychromatic418967fa.accept_10_5_1_6_1_672 75 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 131 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 74 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 131 246 (accept_3_4 73 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 131 246 (Polychromatic418967fa.accept_10_2_1_6_1_634 72 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 131 246
  (Polychromatic418967fa.accept_9_8_5_3_1_777 71 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 131 246 (accept_3_4 70 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 131 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 131 246 (Polychromatic418967fa.accept_16_4_3_6_1_6805 68 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 131 246 (accept_3_4 67 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 131 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 131 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 131 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 131 246 (accept_3_4 64 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 131 246 (Polychromatic418967fa.accept_13_11_1_12_1_742 63 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 131 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 62 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 131 246 (accept_3_4 61 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 131 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 131 246
  (Polychromatic418967fa.accept_7_3_5_1_1_72 59 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 131 246 (accept_3_4 58 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 131 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 131 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 56 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 131 246 (accept_3_4 55 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 131 246 (Polychromatic418967fa.accept_13_2_1_12_1_1326 54 131 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 131 246 (accept_3_4 52 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 131 246 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 131 246 (Polychromatic418967fa.accept_13_11_1_12_1_742 50 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 246 (accept_3_4 49 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 131 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 246
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 131 246 (accept_3_4 46 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 131 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 131 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 44 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 246 (accept_3_4 43 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 246 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 131 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 131 246 (accept_3_4 40 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 131 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 131 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 246 (accept_3_4 37 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 246 (Polychromatic418967fa.accept_16_4_3_6_1_6805 36 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 246
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 131 246 (accept_3_4 34 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 131 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 131 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 246 (accept_3_4 31 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 246 (Polychromatic418967fa.accept_19_11_17_18_1_5236 30 131 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 246 (accept_3_4 28 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 26 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 246 (accept_3_4 25 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 246
  (Polychromatic418967fa.accept_19_4_17_18_1_9536 23 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 131 246 (accept_3_4 22 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 131 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 131 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 131 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 246 (accept_3_4 19 131 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 246 (Polychromatic418967fa.accept_7_4_5_1_1_418
  18 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 246 (accept_3_4 16 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 246 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 246 (Polychromatic418967fa.accept_20_14_11_6_1_6264 14 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 246 (accept_3_4 13 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 246 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 131
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 246
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 246 (accept_3_4 10 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 246 (accept_3_4 7 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 131 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 246 (accept_3_4 4 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 131 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 246 (accept_3_4 1 131 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 117 130 246 (Eq.refl Bool.true) (allA_succ_of_gcd 116 130 246 2 58 65 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 130 246
  (Polychromatic418967fa.accept_7_3_4_1_1_71 115 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 130 246 2 57 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 130 246 (accept_3_5 113 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 130 246 2 56 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 130 246 (Polychromatic418967fa.accept_12_3_10_6_1_442 111 130 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 130 246 2 55 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 130 246
  (Polychromatic418967fa.accept_9_1_4_3_1_201 109 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 130 246 2 54 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 130 246 (accept_3_5 107 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 130 246 2 53 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 130 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 105 130 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 130 246 2 52 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 130 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 103 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 130 246 2 51 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 130 246 (accept_3_5 101 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 130 246 2 50 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 130 246 (Polychromatic418967fa.accept_12_3_10_6_1_442 99 130 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 130 246 2 49 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 130 246
  (Polychromatic418967fa.accept_9_7_4_3_1_204 97 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 130 246 2 48 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 130 246 (accept_3_5 95 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 130 246 2 47 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 130 246 (Polychromatic418967fa.accept_12_9_10_6_1_872 93 130 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 130 246 2 46 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 130 246
  (Polychromatic418967fa.accept_9_1_4_3_1_201 91 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 130 246 2 45 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 130 246 (accept_3_5 89 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 130 246 2 44 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 130 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 130 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 130 246 2 43 65 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 130 246
  (Polychromatic418967fa.accept_19_9_16_18_1_3887 85 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 130 246 2 42 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 130 246 (accept_3_5 83 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 130 246 2 41 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 130 246 (Polychromatic418967fa.accept_12_9_10_6_1_872 81 130 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 130 246 2 40 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 130 246
  (Polychromatic418967fa.accept_9_7_4_3_1_204 79 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 130 246 2 39 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 130 246 (accept_3_5 77 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 130 246 2 38 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 130 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 130 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 130 246 2 37 65 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 130 246
  (Polychromatic418967fa.accept_7_3_4_1_1_71 73 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 130 246 2 36 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 130 246 (accept_3_5 71 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 130 246 2 35 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 130 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 69 130 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 130 246 2 34 65 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 130 246
  (Polychromatic418967fa.accept_14_11_4_8_1_664 67 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 130 246 2 33 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 130 246 (accept_3_5 65 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 130 246 2 32 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 130 246 (Polychromatic418967fa.accept_12_3_10_6_1_442 63 130 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 130 246 2 31 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 130 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 61 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 130 246 2 30 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 130 246 (accept_3_5 59 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 130 246 2 29 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 130 246 (Polychromatic418967fa.accept_11_2_9_4_1_310 57 130 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 130 246 2 28 65 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 130 246
  (Polychromatic418967fa.accept_9_1_4_3_1_201 55 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 130 246 2 27 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 130 246 (accept_3_5 53 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 130 246 2 26 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 130 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 130 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 130 246 2 25 65 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 130 246
  (Polychromatic418967fa.accept_15_4_10_6_1_2997 49 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 130 246 2 24 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 130 246 (accept_3_5 47 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 130 246 2 23 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 130 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 130 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 130 246 2 22 65 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 130 246
  (Polychromatic418967fa.accept_9_7_4_3_1_204 43 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 130 246 2 21 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 130 246 (accept_3_5 41 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 130 246 2 20 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 130 246 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 130 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 130 246 2 19 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 130 246
  (Polychromatic418967fa.accept_9_1_4_3_1_201 37 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 130 246 2 18 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 130 246 (accept_3_5 35 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 130 246 2 17 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 130 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 130 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 130 246 2 16 65 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 130 246
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 130 246 2 15 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 130 246 (accept_3_5 29 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 130 246 2 14 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 130 246 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 130 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 246 2 13 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 130 246
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 130 246 2 12 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 130 246 (accept_3_5 23 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 130 246 2 11 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 130 246 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 130 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 246 2 10 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 246 2 9 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 130 246 (accept_3_5 17 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 130 246 2 8 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 130 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 130 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 130 246 2 7 65 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 130 246
  (Polychromatic418967fa.accept_11_2_9_4_1_310 13 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 130 246 2 6 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 130 246 (accept_3_5 11 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 130 246 2 5 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 130 246 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 130 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 130 246 2 4 65 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 130 246
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 130 246 2 3 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 130 246 (accept_3_5 5 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 130
  246 2 2 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  130 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 130 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 130 246 2 1 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 130 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 130 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 118 129 246 (Eq.refl Bool.true) (allA_succ_of_gcd 117 129 246 3 39 43 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 129 246
  (Polychromatic418967fa.accept_7_4_3_1_1_87 116 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 129 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 115 129 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 129 246 3 38 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 129 246 (Polychromatic418967fa.accept_10_3_9_6_1_94
  113 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 129 246
  (Polychromatic418967fa.accept_12_4_9_6_1_440 112 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 111 129 246 3 37 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 110 129 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 110 129 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 129 246
  (Polychromatic418967fa.accept_7_4_3_1_1_87 109 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 129 246 3 36 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 129 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 107 129 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 129 246 (Polychromatic418967fa.accept_11_7_8_4_1_718
  106 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 129 246 3 35 43 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 129 246
  (Polychromatic418967fa.accept_12_8_9_6_1_127 104 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 129 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 129 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 129 246 3 34 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 129 246
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 101 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 129 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 100 129 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 129 246 3 33 43 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 129 246
  (Polychromatic418967fa.accept_12_2_9_6_1_439 98 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 129 246 (Polychromatic418967fa.accept_17_12_10_8_1_5039 97 129 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 129 246 3 32 43 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 129 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 129 246 (Polychromatic418967fa.accept_12_10_9_6_1_1445 94 129 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 129 246 3 31 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 129 246 (Polychromatic418967fa.accept_12_8_9_6_1_127
  92 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 129 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 91 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 129 246 3 30 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 129 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 129 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 129 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 88
  129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 129 246 3 29 43 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 129 246
  (Polychromatic418967fa.accept_7_2_3_1_1_10 86 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 129 246 (Polychromatic418967fa.accept_10_5_9_6_1_697 85 129 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 129 246 3 28 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 129 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 83
  129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 82 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 129 246 3 27 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 129 246 (Polychromatic418967fa.accept_12_8_9_6_1_127 80 129 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 79
  129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 129 246 3 26 43 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 129 246
  (Polychromatic418967fa.accept_20_17_9_6_1_6219 77 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 129 246 (Polychromatic418967fa.accept_12_4_9_6_1_440 76 129 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 129 246 3 25 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 129 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 74
  129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 246
  (Polychromatic418967fa.accept_10_3_9_6_1_94 73 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 129 246 3 24 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 129 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 129 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 246
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 70 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 129 246 3 23 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 129 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 129 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 67
  129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 129 246 3 22 43 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 129 246
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 129 246 (Polychromatic418967fa.accept_12_4_9_6_1_440 64 129 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 129 246 3 21 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 129 246 (Polychromatic418967fa.accept_11_7_8_4_1_718
  62 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 61 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 129 246 3 20 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 129 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 129 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 58
  129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 129 246 3 19 43 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 129 246
  (Polychromatic418967fa.accept_11_1_8_4_1_717 56 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 129 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 129 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 129 246 3 18 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 129 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 53
  129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 246
  (Polychromatic418967fa.accept_12_4_9_6_1_440 52 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 129 246 3 17 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 129 246 (Polychromatic418967fa.accept_12_2_9_6_1_439 50 129 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 246 (Polychromatic418967fa.accept_15_4_9_6_1_627
  49 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 129 246 3 16 43 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 129 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 129 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 129 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 129 246 3 15 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 129 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 44
  129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 129 246 3 14 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 129 246 (Polychromatic418967fa.accept_15_11_9_6_1_1321 41 129 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 40 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 129 246 3 13 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 129 246 (Polychromatic418967fa.accept_12_2_9_6_1_439 38 129 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 37
  129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 129 246 3 12 43 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 129 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 246 (Polychromatic418967fa.accept_11_1_8_4_1_717 34 129 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 129 246 3 11 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 129 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 32
  129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 129 246 3 10 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 129 246 (Polychromatic418967fa.accept_11_7_8_4_1_718 29 129 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 246 (Polychromatic418967fa.accept_12_4_9_6_1_440
  28 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 129 246 3 9 43 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 129 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 129 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 129 246 3 8 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 129 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 246
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 129 246 3 7 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 129 246 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 129 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 129 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 129 246 3 6 43 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 129 246
  (Polychromatic418967fa.accept_20_17_9_6_1_6219 17 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 129 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 129 246 3 5 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 129 246 (Polychromatic418967fa.accept_12_2_9_6_1_439
  14 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 246
  (Polychromatic418967fa.accept_10_3_9_6_1_94 13 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 129 246 3 4 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 129 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 129 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 246 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 129
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 246 3 3 43 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 246
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 129 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 246 3 2 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 129 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 246
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 129 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 129 246 3 1 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 129 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 129 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 246 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 129 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 128 246 (Eq.refl Bool.true) (allA_succ_of_gcd 118 128 246 2 59 64 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 128 246
  (Polychromatic418967fa.accept_12_9_8_6_1_466 117 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 128 246 2 58 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 128 246 (accept_3_4 115 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 128 246 2 57 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 128 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 113 128 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 128 246 2 56 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 128 246
  (Polychromatic418967fa.accept_7_6_2_1_1_214 111 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 128 246 2 55 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 128 246 (accept_3_4 109 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 128 246 2 54 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 128 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 107 128 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 128 246 2 53 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 128 246
  (Polychromatic418967fa.accept_9_6_2_3_1_771 105 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 128 246 2 52 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 128 246 (accept_3_4 103 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 128 246 2 51 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 128 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 101 128 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 128 246 2 50 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 128 246
  (Polychromatic418967fa.accept_12_3_8_6_1_895 99 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 128 246 2 49 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 128 246 (accept_3_4 97 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 128 246 2 48 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 128 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 95 128 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 128 246 2 47 64 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 128 246
  (Polychromatic418967fa.accept_10_3_8_6_1_326 93 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 128 246 2 46 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 128 246 (accept_3_4 91 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 128 246 2 45 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 128 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 89 128 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 128 246 2 44 64 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 128 246
  (Polychromatic418967fa.accept_7_3_2_1_1_225 87 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 128 246 2 43 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 128 246 (accept_3_4 85 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 128 246 2 42 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 128 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 128 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 128 246 2 41 64 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 128 246
  (Polychromatic418967fa.accept_12_9_8_6_1_466 81 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 128 246 2 40 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 128 246 (accept_3_4 79 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 128 246 2 39 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 128 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 77 128 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 128 246 2 38 64 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 128 246
  (Polychromatic418967fa.accept_12_3_8_6_1_895 75 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 128 246 2 37 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 128 246 (accept_3_4 73 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 128 246 2 36 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 128 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 71 128 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 128 246 2 35 64 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 128 246
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 128 246 2 34 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 128 246 (accept_3_4 67 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 128 246 2 33 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 128 246 (Polychromatic418967fa.accept_24_17_8_6_1_6246 65 128 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 128 246 2 32 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 128 246
  (Polychromatic418967fa.accept_10_3_8_6_1_326 63 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 128 246 2 31 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 128 246 (accept_3_4 61 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 128 246 2 30 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 128 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 128 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 128 246 2 29 64 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 128 246
  (Polychromatic418967fa.accept_12_9_8_6_1_466 57 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 128 246 2 28 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 128 246 (accept_3_4 55 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 128 246 2 27 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 128 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 128 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 246 2 26 64 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 246
  (Polychromatic418967fa.accept_9_6_2_3_1_771 51 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 128 246 2 25 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 128 246 (accept_3_4 49 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 128 246 2 24 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 128 246 (Polychromatic418967fa.accept_11_3_7_4_1_1133 47 128 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 128 246 2 23 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 128 246
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 128 246 2 22 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 128 246 (accept_3_4 43 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 128 246 2 21 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 128 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 128 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 246 2 20 64 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 246
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 246 2 19 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 246 (accept_3_4 37 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 246 2 18 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 128 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 128 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 246 2 17 64 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 246
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 128 246 2 16 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 128 246 (accept_3_4 31 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 128 246 2 15 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 128 246 (Polychromatic418967fa.accept_14_1_2_8_1_655 29 128 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 246 2 14 64 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 246
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 128 246 2 13 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 128 246 (accept_3_4 25 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 246 2 12 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 128 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 128 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 246 2 11 64 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 246
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 246 2 10 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 128 246 (accept_3_4 19 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 128 246 2 9 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 128 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 128 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 246 2 8 64 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 246
  (Polychromatic418967fa.accept_9_6_2_3_1_771 15 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 128 246 2 7 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 128 246 (accept_3_4 13 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 128 246 2 6 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 128 246 (Polychromatic418967fa.accept_17_11_9_8_1_5038 11 128 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 128 246 2 5 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 128 246
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 128 246 2 4 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 128 246 (accept_3_4 7 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128
  246 2 3 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  128 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 128 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 128 246 2 2 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 128 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 128 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 246 2 1 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 246 (accept_3_4 1 128 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 120 127 246 (Eq.refl Bool.true) (allA_succ_of_accept 119 127 246 (accept_3_5 119 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 127 246 (Polychromatic418967fa.accept_15_13_7_6_1_682 118 127
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 127 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 117 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 127 246 (accept_3_5 116 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 127 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 115 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 127 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 114 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 127 246 (accept_3_5 113 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 127 246 (Polychromatic418967fa.accept_9_4_1_3_1_190 112 127
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 127 246
  (Polychromatic418967fa.accept_10_1_7_6_1_91 111 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 127 246 (accept_3_5 110 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 127 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 127 246 (Polychromatic418967fa.accept_21_3_1_15_1_4287 108 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 127 246 (accept_3_5 107 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 127 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 106 127
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 127 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 105 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 127 246 (accept_3_5 104 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 127 246 (Polychromatic418967fa.accept_9_4_1_3_1_190 103 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 127 246 (Polychromatic418967fa.accept_13_11_10_12_1_1338 102 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 127 246 (accept_3_5 101 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 127 246 (Polychromatic418967fa.accept_13_9_10_12_1_2048 100
  127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 127 246
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 99 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 127 246 (accept_3_5 98 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 127 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 127 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 127 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 96 127 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 127 246 (accept_3_5 95 127 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 127 246 (Polychromatic418967fa.accept_9_4_1_3_1_190
  94 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 127 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 127 246 (accept_3_5 92 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 127 246 (Polychromatic418967fa.accept_10_1_7_6_1_91 91 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 127 246 (Polychromatic418967fa.accept_11_2_6_4_1_3028 90 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 127 246 (accept_3_5 89 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 127 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 88 127 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 127 246
  (Polychromatic418967fa.accept_9_6_1_3_1_191 87 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 127 246 (accept_3_5 86 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 127 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 127 246 (Polychromatic418967fa.accept_13_6_10_12_1_2049 84 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 127 246 (accept_3_5 83 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 127 246 (Polychromatic418967fa.accept_21_19_1_15_1_11887 82
  127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 127 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 127 246 (accept_3_5 80 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 127 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 79 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 127 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 78 127 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 127 246 (accept_3_5 77 127 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 127 246 (Polychromatic418967fa.accept_9_4_1_3_1_190 76 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 127 246
  (Polychromatic418967fa.accept_18_3_1_12_1_4419 75 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 127 246 (accept_3_5 74 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 127 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 127 246 (Polychromatic418967fa.accept_13_7_10_12_1_2047 72 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 127 246 (accept_3_5 71 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 127 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 70 127 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 127 246 (accept_3_5 68 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 127 246 (Polychromatic418967fa.accept_9_4_1_3_1_190 67 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 127 246 (Polychromatic418967fa.accept_19_9_13_18_1_10812 66 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 246 (accept_3_5 65 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 127 246 (Polychromatic418967fa.accept_22_20_17_4_1_10199 64
  127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 127 246
  (Polychromatic418967fa.accept_10_3_7_6_1_659 63 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 127 246 (accept_3_5 62 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 127 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 127 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 60 127 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 127 246 (accept_3_5 59 127 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 127 246 (Polychromatic418967fa.accept_9_4_1_3_1_190 58 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 127 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 127 246 (accept_3_5 56 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 127 246 (Polychromatic418967fa.accept_16_7_15_6_1_1428 55 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 127 246 (Polychromatic418967fa.accept_13_2_10_12_1_757 54 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 127 246 (accept_3_5 53 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 127 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 52 127 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 127 246
  (Polychromatic418967fa.accept_9_6_1_3_1_191 51 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 127 246 (accept_3_5 50 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 127 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 127 246 (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 246 (accept_3_5 47 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 246 (Polychromatic418967fa.accept_11_2_6_4_1_3028 46 127
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 127 246 (accept_3_5 44 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 127 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 127 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 127 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 246 (accept_3_5 41 127 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 246 (Polychromatic418967fa.accept_9_4_1_3_1_190 40 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 246
  (Polychromatic418967fa.accept_16_7_15_6_1_1428 39 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 127 246 (accept_3_5 38 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 127 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 127 246 (Polychromatic418967fa.accept_19_17_13_18_1_9542 36 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 246 (accept_3_5 35 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 127 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 127 246 (accept_3_5 32 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 127 246 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 127 246 (Polychromatic418967fa.accept_14_2_1_8_1_650 30 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 246 (accept_3_5 29 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 246 (Polychromatic418967fa.accept_13_2_10_12_1_757 28 127
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 246
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 27 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 127 246 (accept_3_5 26 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 127 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 127 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 127 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 246 (accept_3_5 23 127 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 246 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 246 (accept_3_5 20 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 246 (Polychromatic418967fa.accept_13_6_10_12_1_2049 19 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 246 (Polychromatic418967fa.accept_21_18_1_15_1_11930 18 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 246 (accept_3_5 17 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 127 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 246
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 246 (accept_3_5 14 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 246 (Polychromatic418967fa.accept_15_12_7_6_1_4013 12 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 246 (accept_3_5 11 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 246 (Polychromatic418967fa.accept_21_10_1_15_1_10541 10
  127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 246 (accept_3_5 8 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 127 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 246 (accept_3_5 5 127 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 246 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 127 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 246
  (Polychromatic418967fa.accept_10_3_7_6_1_659 3 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 246 (accept_3_5 2 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 127 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 121 126 246 (Eq.refl Bool.true) (allA_succ_of_gcd 120 126 246 6 20 21 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 126 246
  (Polychromatic418967fa.accept_22_9_16_4_1_8629 119 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 118 126 246 2 59 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 117 126 246 3 39 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 116 126 246 2 58 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 126 246
  (Polychromatic418967fa.accept_19_1_12_18_1_10820 115 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 126 246 6 19 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 126 246 (Polychromatic418967fa.accept_23_21_11_16_1_14804 113 126 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 126 246 2 56 63 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 111 126 246 3 37 42 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 110 126 246 2 55 63
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 126 246
  (Polychromatic418967fa.accept_11_10_5_4_1_711 109 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 126 246 6 18 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 126 246 (Polychromatic418967fa.accept_13_3_9_12_1_2062 107 126 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 126 246 2 53 63 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 126 246 3 35 42 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 126 246 2 52 63 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 126 246
  (Polychromatic418967fa.accept_17_1_7_8_1_6347 103 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 126 246 6 17 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 126 246 (Polychromatic418967fa.accept_13_10_9_12_1_2814 101 126 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 126 246 2 50 63 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 126 246 3 33 42 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 126 246 2 49 63 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 126 246
  (Polychromatic418967fa.accept_22_9_16_4_1_8629 97 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 126 246 6 16 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 126 246 (Polychromatic418967fa.accept_25_20_1_21_1_14803 95 126 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 126 246 2 47 63 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 126 246 3 31 42 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 126 246 2 46 63 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 126 246
  (Polychromatic418967fa.accept_19_15_12_18_1_6634 91 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 126 246 6 15 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 126 246 (Polychromatic418967fa.accept_17_4_7_8_1_7491 89 126 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 126 246 2 44 63 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 126 246 3 29 42 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 126 246 2 43 63 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 126 246
  (Polychromatic418967fa.accept_19_9_12_18_1_8099 85 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 126 246 6 14 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 126 246 (Polychromatic418967fa.accept_19_7_12_18_1_10848 83 126 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 126 246 2 41 63 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 126 246 3 27 42 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 126 246 2 40 63
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 126 246
  (Polychromatic418967fa.accept_25_4_1_21_1_14802 79 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 126 246 6 13 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 126 246 (Polychromatic418967fa.accept_19_1_12_18_1_10820 77 126 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 126 246 2 38 63 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 126 246 3 25 42 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 126 246 2 37 63
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 126 246
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 73 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 246 6 12 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 126 246 (Polychromatic418967fa.accept_27_17_18_3_1_14801 71 126 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 126 246 2 35 63 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 126 246 3 23 42 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 126 246 2 34 63 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 126 246
  (Polychromatic418967fa.accept_17_16_7_8_1_7638 67 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 246 6 11 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 246 (Polychromatic418967fa.accept_11_10_5_4_1_711 65 126 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 126 246 2 32 63 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 126 246 3 21 42 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 126 246 2 31 63 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 126 246
  (Polychromatic418967fa.accept_25_11_1_21_1_13143 61 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 126 246 6 10 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 126 246 (Polychromatic418967fa.accept_22_15_16_4_1_8643 59 126 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 246 2 29 63 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 126 246 3 19 42 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 126 246 2 28 63
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 126 246
  (Polychromatic418967fa.accept_13_3_9_12_1_2062 55 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 246 6 9 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 126 246 (Polychromatic418967fa.accept_19_15_12_18_1_6634 53 126 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 246 2 26 63 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 126 246 3 17 42 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 126 246 2 25 63 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 126 246
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 49 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 126 246 6 8 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 126 246 (Polychromatic418967fa.accept_13_8_9_12_1_2813 47 126 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 246 2 23 63 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 126 246 3 15 42 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 126 246 2 22 63 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 246
  (Polychromatic418967fa.accept_11_10_5_4_1_711 43 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 246 6 7 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 126 246 (Polychromatic418967fa.accept_22_19_16_4_1_10248 41 126 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 246 2 20 63 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 126 246 3 13 42 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 126 246 2 19 63 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 246
  (Polychromatic418967fa.accept_22_15_16_4_1_8643 37 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 126 246 6 6 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 126 246 (Polychromatic418967fa.accept_17_1_7_8_1_6347 35 126 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 246 2 17 63 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 126 246 3 11 42 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 126 246 2 16 63 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 246
  (Polychromatic418967fa.accept_17_14_7_8_1_7544 31 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 246 6 5 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 126 246 (Polychromatic418967fa.accept_13_3_9_12_1_2062 29 126 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 246 2 14 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 126 246 3 9 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 126 246 2 13 63 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 246
  (Polychromatic418967fa.accept_19_6_12_18_1_8141 25 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 126 246 6 4 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 126 246 (Polychromatic418967fa.accept_13_10_9_12_1_2814 23 126 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 246 2 11 63 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 126 246 3 7 42 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 126 246 2 10 63 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 246
  (Polychromatic418967fa.accept_22_19_16_4_1_10248 19 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 126 246 6 3 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 126 246 (Polychromatic418967fa.accept_19_17_12_18_1_5248 17 126 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 246 2 8 63 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 126 246 3 5 42 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 126 246 2 7 63 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 246
  (Polychromatic418967fa.accept_19_13_12_18_1_2677 13 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 126 246 6 2 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 126 246 (Polychromatic418967fa.accept_19_11_12_18_1_3893 11 126 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 246 2 5 63 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 126 246 3 3 42 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 126 246 2 4 63 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 246
  (Polychromatic418967fa.accept_19_7_12_18_1_10848 7 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 126 246 6 1 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 126 246 (Polychromatic418967fa.accept_23_5_11_16_1_6597 5 126 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 246 2 2 63 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 126 246 3 1 42 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 126 246 2 1 63 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 246
  (Polychromatic418967fa.accept_17_1_7_8_1_6347 1 126 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 126
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 122 125 246 (Eq.refl Bool.true) (allA_succ_of_accept 121 125 246 (accept_3_4 121 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 125 246 (Polychromatic418967fa.accept_19_6_11_18_1_12181 120
  125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 125 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 119 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 125 246 (accept_3_4 118 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 125 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 117 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 125 246 (Polychromatic418967fa.accept_15_11_5_6_1_669 116 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 125 246 (accept_3_4 115 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 125 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 114 125
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 125 246
  (Polychromatic418967fa.accept_9_5_8_3_1_437 113 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 125 246 (accept_3_4 112 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 125 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 125 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 110 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 125 246 (accept_3_4 109 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 125 246 (Polychromatic418967fa.accept_13_4_8_12_1_3526 108
  125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 125 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 107 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 125 246 (accept_3_4 106 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 125 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 105 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 125 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 104 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 125 246 (accept_3_4 103 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 125 246 (Polychromatic418967fa.accept_15_12_5_6_1_2148 102
  125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 125 246
  (Polychromatic418967fa.accept_9_2_8_3_1_181 101 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 125 246 (accept_3_4 100 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 125 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 125 246 (Polychromatic418967fa.accept_13_7_8_12_1_2810 98 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 125 246 (accept_3_4 97 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 125 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 96 125 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 125 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 125 246 (accept_3_4 94 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 125 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 125 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 92 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 125 246 (accept_3_4 91 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 125 246 (Polychromatic418967fa.accept_20_10_5_6_1_12032 90 125 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 125 246
  (Polychromatic418967fa.accept_7_5_6_1_1_407 89 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 125 246 (accept_3_4 88 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 125 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 125 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 86 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 125 246 (accept_3_4 85 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 125 246 (Polychromatic418967fa.accept_10_4_5_6_1_651 84 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 125 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 125 246 (accept_3_4 82 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 125 246 (Polychromatic418967fa.accept_10_1_5_6_1_649 81 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 125 246 (Polychromatic418967fa.accept_19_4_11_18_1_3909 80 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 125 246 (accept_3_4 79 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 125 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 78 125 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 125 246
  (Polychromatic418967fa.accept_9_5_8_3_1_437 77 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 125 246 (accept_3_4 76 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 125 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 125 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 74 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 125 246 (accept_3_4 73 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 125 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 125 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 125 246 (accept_3_4 70 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 125 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 125 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 125 246 (accept_3_4 67 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 125 246 (Polychromatic418967fa.accept_13_1_8_12_1_2045 66 125 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 125 246
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 125 246 (accept_3_4 64 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 125 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 125 246 (Polychromatic418967fa.accept_13_10_8_12_1_2032 62 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 246 (accept_3_4 61 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 125 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 125 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 125 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 125 246 (accept_3_4 58 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 125 246 (Polychromatic418967fa.accept_13_5_8_12_1_2759 57 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 125 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 56 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 125 246 (accept_3_4 55 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 125 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 125 246
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 53 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 125 246 (accept_3_4 52 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 125 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 125 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 50 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 125 246 (accept_3_4 49 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 125 246 (Polychromatic418967fa.accept_13_9_8_12_1_2031 48 125 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 125 246 (accept_3_4 46 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 125 246 (Polychromatic418967fa.accept_18_9_17_12_1_462 45 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 125 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 246 (accept_3_4 43 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 125 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 246
  (Polychromatic418967fa.accept_9_5_8_3_1_437 41 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 125 246 (accept_3_4 40 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 125 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 125 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 38 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 246 (accept_3_4 37 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 246 (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 125 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 125 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 125 246 (accept_3_4 34 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 125 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 125 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 32 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 246 (accept_3_4 31 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 125 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 125 246
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 125 246 (accept_3_4 28 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 125 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 125 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 246 (accept_3_4 25 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 125 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 125 246 (accept_3_4 22 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 125 246 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 125 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 246 (accept_3_4 19 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 246 (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 125 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 246
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 17 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 246 (accept_3_4 16 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 125 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 125 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 246 (accept_3_4 13 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 125 246 (accept_3_4 10 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  125 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 125 246 (Polychromatic418967fa.accept_19_8_11_18_1_14800 8 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 246 (accept_3_4 7 125 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 125 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 246
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 246 (accept_3_4 4 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 125 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 246 (accept_3_4 1 125 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 125
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 123 124 246 (Eq.refl Bool.true) (allA_succ_of_gcd 122 124 246 2 61 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 124 246
  (Polychromatic418967fa.accept_9_4_7_3_1_43 121 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 124 246 2 60 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 124 246 (accept_3_5 119 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 124 246 2 59 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 124 246 (Polychromatic418967fa.accept_11_7_3_4_1_729 117 124 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 124 246 2 58 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 124 246
  (Polychromatic418967fa.accept_7_3_5_1_1_72 115 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 124 246 2 57 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 124 246 (accept_3_5 113 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 124 246 2 56 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 124 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 111 124 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 124 246 2 55 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 124 246
  (Polychromatic418967fa.accept_7_4_5_1_1_418 109 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 124 246 2 54 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 124 246 (accept_3_5 107 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 124 246 2 53 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 124 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 105 124 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 124 246 2 52 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 124 246
  (Polychromatic418967fa.accept_9_4_7_3_1_43 103 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 124 246 2 51 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 124 246 (accept_3_5 101 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 124 246 2 50 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 124 246 (Polychromatic418967fa.accept_12_3_4_6_1_434 99 124 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 124 246 2 49 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 124 246
  (Polychromatic418967fa.accept_7_6_5_1_1_416 97 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 124 246 2 48 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 124 246 (accept_3_5 95 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 124 246 2 47 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 124 246 (Polychromatic418967fa.accept_12_9_4_6_1_460 93 124 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 124 246 2 46 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 124 246
  (Polychromatic418967fa.accept_9_1_7_3_1_41 91 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 124 246 2 45 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 124 246 (accept_3_5 89 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 124 246 2 44 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 124 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 124 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 124 246 2 43 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 124 246
  (Polychromatic418967fa.accept_9_4_7_3_1_43 85 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 124 246 2 42 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 124 246 (accept_3_5 83 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 124 246 2 41 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 124 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 124 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 124 246 2 40 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 124 246
  (Polychromatic418967fa.accept_22_13_14_4_1_10191 79 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 124 246 2 39 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 124 246 (accept_3_5 77 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 124 246 2 38 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 124 246 (Polychromatic418967fa.accept_10_5_4_6_1_319 75 124 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 124 246 2 37 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 124 246
  (Polychromatic418967fa.accept_7_3_5_1_1_72 73 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 124 246 2 36 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 124 246 (accept_3_5 71 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 124 246 2 35 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 124 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 124 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 124 246 2 34 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 124 246
  (Polychromatic418967fa.accept_7_4_5_1_1_418 67 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 124 246 2 33 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 124 246 (accept_3_5 65 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 124 246 2 32 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 124 246 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 124 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 124 246 2 31 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 124 246
  (Polychromatic418967fa.accept_25_11_24_21_1_4074 61 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 124 246 2 30 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 124 246 (accept_3_5 59 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 124 246 2 29 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 124 246 (Polychromatic418967fa.accept_12_9_4_6_1_460 57 124 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 124 246 2 28 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 124 246
  (Polychromatic418967fa.accept_7_6_5_1_1_416 55 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 124 246 2 27 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 124 246 (accept_3_5 53 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 124 246 2 26 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 124 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 124 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 124 246 2 25 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 124 246
  (Polychromatic418967fa.accept_9_4_7_3_1_43 49 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 124 246 2 24 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 124 246 (accept_3_5 47 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 124 246 2 23 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 124 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 124 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 246 2 22 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 246
  (Polychromatic418967fa.accept_13_4_7_12_1_2823 43 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 124 246 2 21 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 124 246 (accept_3_5 41 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 246 2 20 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 124 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 246 2 19 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 246
  (Polychromatic418967fa.accept_9_1_7_3_1_41 37 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 246 2 18 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 124 246 (accept_3_5 35 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 124 246 2 17 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 124 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 124 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 246 2 16 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 246
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 124 246 2 15 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 124 246 (accept_3_5 29 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 124 246 2 14 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 124 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 124 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 124 246 2 13 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 124 246
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 124 246 2 12 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 124 246 (accept_3_5 23 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 124 246 2 11 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 124 246 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 124 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 124 246 2 10 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 246
  (Polychromatic418967fa.accept_9_1_7_3_1_41 19 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 124 246 2 9 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 124 246 (accept_3_5 17 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 124 246 2 8 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 124 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 124 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 124 246 2 7 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 124 246
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 124 246 2 6 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 124 246 (accept_3_5 11 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 124 246 2 5 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 124 246 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 124 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 246 2 4 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 246
  (Polychromatic418967fa.accept_11_7_3_4_1_729 7 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 124 246 2 3 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 124 246 (accept_3_5 5 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124
  246 2 2 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  124 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 124 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 124 246 2 1 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 124 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 124 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 123 246 (allA_succ_of_accept 122 123 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 122 123 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 123 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 121 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 123 246 3 40 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 123 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 119 123 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 123 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 118 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 117 123 246 3 39 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 116 123 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 116 123 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 123 246
  (Polychromatic418967fa.accept_7_3_4_1_1_71 115 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 123 246 3 38 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 123 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 113 123 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 123 246 (Polychromatic418967fa.accept_9_4_6_3_1_179
  112 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 123 246 3 37 41 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 123 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 110 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 123 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 123 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 123 246 3 36 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 123 246 (Polychromatic418967fa.accept_9_8_6_3_1_457
  107 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 123 246
  (Polychromatic418967fa.accept_9_7_6_3_1_456 106 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 123 246 3 35 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 123 246 (Polychromatic418967fa.accept_9_5_6_3_1_40 104 123 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 123 246 (Polychromatic418967fa.accept_7_5_4_1_1_412
  103 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 123 246 3 34 41 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 123 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 123 246 (Polychromatic418967fa.accept_9_1_6_3_1_177 100 123 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 123 246 3 33 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 123 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 98
  123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 97 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 123 246 3 32 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 123 246 (Polychromatic418967fa.accept_9_5_6_3_1_40 95 123 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 123 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 94
  123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 123 246 3 31 41 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 123 246
  (Polychromatic418967fa.accept_9_2_6_3_1_178 92 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 123 246 (Polychromatic418967fa.accept_9_1_6_3_1_177 91 123 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 123 246 3 30 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 123 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 89
  123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 123 246
  (Polychromatic418967fa.accept_9_7_6_3_1_456 88 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 123 246 3 29 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 123 246 (Polychromatic418967fa.accept_9_5_6_3_1_40 86 123 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 85
  123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 123 246 3 28 41 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 123 246
  (Polychromatic418967fa.accept_9_2_6_3_1_178 83 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 123 246 41 2 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 81 123 246 3 27 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 123 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 80 123 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 246 (Polychromatic418967fa.accept_9_7_6_3_1_456
  79 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 123 246 3 26 41 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 123 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 123 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 76 123 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 123 246 3 25 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 123 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 74
  123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 73 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 123 246 3 24 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 123 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 71 123 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 123 246 (Polychromatic418967fa.accept_9_7_6_3_1_456
  70 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 123 246 3 23 41 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 123 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 68 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 123 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 67 123 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 123 246 3 22 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 123 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 65
  123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 64 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 123 246 3 21 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 123 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 62 123 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 61
  123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 123 246 3 20 41 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 123 246
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 123 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 58 123 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 123 246 3 19 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 123 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 56
  123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 55 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 123 246 3 18 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 123 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 123 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 52
  123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 123 246 3 17 41 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 123 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 50 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 123 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 123 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 123 246 3 16 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 123 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 47
  123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 46 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 123 246 3 15 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 123 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 44 123 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 246 (Polychromatic418967fa.accept_9_7_6_3_1_456
  43 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 123 246 3 14 41 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 41 123 246 41 1 3 6
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 40 123 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 40 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 123 246 3 13 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 123 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 123 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 123 246 3 12 41 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 123 246
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 246 (Polychromatic418967fa.accept_9_7_6_3_1_456 34 123 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 123 246 3 11 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 123 246 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 246
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 123 246 3 10 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 123 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 123 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 246 (Polychromatic418967fa.accept_9_1_6_3_1_177
  28 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 123 246 3 9 41 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 123 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 123 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 123 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 123 246 3 8 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 123 246 (Polychromatic418967fa.accept_9_5_6_3_1_40 23
  123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 246
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 123 246 3 7 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 123 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 123 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 123 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 246 3 6 41 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 246 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 123 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 123 246 3 5 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 123 246 (Polychromatic418967fa.accept_9_5_6_3_1_40 14
  123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 123 246 3 4 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 123 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 123 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 123 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 246 3 3 41 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 246
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 246 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 123 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 246 3 2 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 123 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 246
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 123 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 123 246 3 1 41 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 123 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 123 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 123 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 122 246 (allA_succ_of_accept 121 122 246 (accept_3_4 121 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 122 246 2 60 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 122 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 119 122 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 122 246 2 59 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 122 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 117 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 122 246 2 58 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 122 246 (accept_3_4 115 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 122 246 2 57 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 122 246 (Polychromatic418967fa.accept_15_8_2_6_1_2125 113 122 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 122 246 2 56 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 122 246
  (Polychromatic418967fa.accept_10_1_2_6_1_638 111 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 122 246 2 55 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 122 246 (accept_3_4 109 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 122 246 2 54 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 122 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 107 122 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 122 246 2 53 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 122 246
  (Polychromatic418967fa.accept_9_6_5_3_1_205 105 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 122 246 2 52 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 122 246 (accept_3_4 103 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 122 246 2 51 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 122 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 101 122 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 122 246 2 50 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 122 246
  (Polychromatic418967fa.accept_12_3_2_6_1_138 99 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 122 246 2 49 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 122 246 (accept_3_4 97 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 122 246 2 48 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 122 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 95 122 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 122 246 2 47 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 122 246
  (Polychromatic418967fa.accept_7_2_3_1_1_10 93 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 122 246 2 46 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 122 246 (accept_3_4 91 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 122 246 2 45 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 122 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 122 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 122 246 2 44 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 122 246
  (Polychromatic418967fa.accept_9_6_5_3_1_205 87 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 122 246 2 43 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 122 246 (accept_3_4 85 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 122 246 2 42 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 122 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 83 122 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 122 246 2 41 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 122 246
  (Polychromatic418967fa.accept_7_4_3_1_1_87 81 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 122 246 2 40 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 122 246 (accept_3_4 79 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 122 246 2 39 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 122 246 (Polychromatic418967fa.accept_19_1_8_18_1_6667 77 122 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 122 246 2 38 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 122 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 75 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 122 246 2 37 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 122 246 (accept_3_4 73 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 122 246 2 36 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 122 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 71 122 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 122 246 2 35 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 122 246
  (Polychromatic418967fa.accept_9_6_5_3_1_205 69 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 122 246 2 34 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 122 246 (accept_3_4 67 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 122 246 2 33 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 122 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 122 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 122 246 2 32 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 246
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 63 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 122 246 2 31 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 122 246 (accept_3_4 61 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 246 2 30 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 246 (Polychromatic418967fa.accept_13_7_5_12_1_1305 59 122 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 246 2 29 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 246
  (Polychromatic418967fa.accept_12_9_2_6_1_455 57 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 246 2 28 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 246 (accept_3_4 55 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 246 2 27 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 122 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 246 2 26 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 246
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 246 2 25 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 246 (accept_3_4 49 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 246 2 24 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 122 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 246 2 23 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 246
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 246 2 22 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 246 (accept_3_4 43 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 246 2 21 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 246 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 122 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 246 2 20 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 246
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 246 2 19 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 246 (accept_3_4 37 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 246 2 18 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 122 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 246 2 17 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 246 2 16 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 246 (accept_3_4 31 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 246 2 15 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 122 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 246 2 14 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 246
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 246 2 13 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 246 (accept_3_4 25 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 246 2 12 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 122 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 246 2 11 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 246
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 246 2 10 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 246 (accept_3_4 19 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 246 2 9 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 122 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 122 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 246 2 8 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 246
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 122 246 2 7 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 122 246 (accept_3_4 13 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 122 246 2 6 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 122 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 122 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 122 246 2 5 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 122 246
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 122 246 2 4 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 122 246 (accept_3_4 7 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122
  246 2 3 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  122 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 122 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 122 246 2 2 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 122 246 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 122 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 246 2 1 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 246 (accept_3_4 1 122 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 246 (allA_succ_of_accept 120 121 246 (Polychromatic418967fa.accept_13_3_4_12_1_36 120 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 121 246 (accept_3_5 119 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 121 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 118 121
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 121 246
  (Polychromatic418967fa.accept_10_7_1_6_1_673 117 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 121 246 (accept_3_5 116 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 121 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 115 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 121 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 114 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 121 246 (accept_3_5 113 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 121 246 (Polychromatic418967fa.accept_10_2_1_6_1_634 112 121
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 121 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 111 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 121 246 (accept_3_5 110 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 121 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 109 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 121 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 108 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 121 246 (accept_3_5 107 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 121 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 106 121
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 121 246
  (Polychromatic418967fa.accept_9_6_4_3_1_203 105 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 121 246 (accept_3_5 104 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 121 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 121 246 (Polychromatic418967fa.accept_10_2_1_6_1_634 102 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 121 246 (accept_3_5 101 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 121 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 100 121
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 121 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 121 246 (accept_3_5 98 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 121 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 97 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 121 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 96 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 121 246 (accept_3_5 95 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 121 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 94 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 121 246
  (Polychromatic418967fa.accept_13_2_4_12_1_745 93 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 121 246 (accept_3_5 92 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 121 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 121 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 90 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 121 246 (accept_3_5 89 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 121 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 88 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 121 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 121 246 (accept_3_5 86 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 121 246 (Polychromatic418967fa.accept_10_5_1_6_1_672 85 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 121 246 (Polychromatic418967fa.accept_15_9_1_6_1_657 84 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 246 (accept_3_5 83 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 121 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 82 121 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 121 246
  (Polychromatic418967fa.accept_13_3_4_12_1_36 81 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 121 246 (accept_3_5 80 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 121 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 121 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 78 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 121 246 (accept_3_5 77 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 121 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 76 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 121 246 (accept_3_5 74 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 121 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 73 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 121 246 (Polychromatic418967fa.accept_10_2_1_6_1_634 72 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 246 (accept_3_5 71 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 121 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 246
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 121 246 (accept_3_5 68 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 121 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 121 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 121 246 (accept_3_5 65 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 121 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 64 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 121 246 (accept_3_5 62 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 121 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 61 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 121 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 60 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 246 (accept_3_5 59 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 246 (Polychromatic418967fa.accept_19_1_7_18_1_10869 58 121 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 246
  (Polychromatic418967fa.accept_10_7_1_6_1_673 57 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 246 (accept_3_5 56 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 246 (Polychromatic418967fa.accept_13_2_4_12_1_745 54 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 246 (accept_3_5 53 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 121 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 246 (accept_3_5 50 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 246 (Polychromatic418967fa.accept_19_11_7_18_1_5284 49 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 246 (accept_3_5 47 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 246
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 246 (accept_3_5 44 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 246 (accept_3_5 41 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 246 (Polychromatic418967fa.accept_15_10_1_6_1_3033 40 121 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 246 (accept_3_5 38 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 246 (Polychromatic418967fa.accept_19_17_7_18_1_6629 36 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 246 (accept_3_5 35 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 121 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 246
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 246 (accept_3_5 32 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 246 (Polychromatic418967fa.accept_19_11_7_18_1_5284 30 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 246 (accept_3_5 29 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 121 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 246 (accept_3_5 26 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 246 (accept_3_5 23 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 246 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 246
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 21 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 246 (accept_3_5 20 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 246 (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 246 (accept_3_5 17 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 121 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 246 (accept_3_5 14 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 246 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 246 (accept_3_5 11 121 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 121 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 246
  (Polychromatic418967fa.accept_15_9_1_6_1_657 9 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 246 (accept_3_5 8 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 246 (accept_3_5 5 121 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 246 (Polychromatic418967fa.accept_31_4_28_29_1_14799 4 121 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 246 (accept_3_5 2 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 121 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 120 246 (allA_succ_of_accept 119 120 246 (Polychromatic418967fa.accept_13_2_3_12_1_735 119 120 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 120 246 2 59 60 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 117 120 246 3 39 40 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 116 120 246 2 58 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 120 246
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 115 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 120 246 6 19 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 120 246 (Polychromatic418967fa.accept_13_9_3_12_1_2025 113 120 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 120 246 2 56 60 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 111 120 246 3 37 40 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 110 120 246 2 55 60
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 120 246
  (Polychromatic418967fa.accept_17_7_1_8_1_6280 109 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 120 246 6 18 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 120 246 (Polychromatic418967fa.accept_19_12_6_18_1_8095 107 120 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 120 246 2 53 60 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 120 246 3 35 40 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 120 246 2 52 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 120 246
  (Polychromatic418967fa.accept_22_15_10_4_1_10294 103 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 120 246 6 17 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 120 246 (Polychromatic418967fa.accept_23_9_5_16_1_4895 101 120 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 120 246 2 50 60 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 120 246 3 33 40 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 120 246 2 49 60
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 120 246
  (Polychromatic418967fa.accept_27_16_12_3_1_14798 97 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 120 246 6 16 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 120 246 (Polychromatic418967fa.accept_13_4_3_12_1_2066 95 120 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 120 246 2 47 60 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 120 246 3 31 40 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 120 246 2 46 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 120 246
  (Polychromatic418967fa.accept_25_16_20_21_1_14797 91 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 120 246 6 15 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 120 246 (Polychromatic418967fa.accept_17_4_1_8_1_5070 89 120 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 120 246 2 44 60 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 120 246 3 29 40 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 120 246 2 43 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 120 246
  (Polychromatic418967fa.accept_19_9_6_18_1_730 85 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 120 246 6 14 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 120 246 (Polychromatic418967fa.accept_19_7_6_18_1_8123 83 120 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 120 246 2 41 60 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 120 246 3 27 40 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 120 246 2 40 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 120 246
  (Polychromatic418967fa.accept_17_11_1_8_1_7502 79 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 120 246 6 13 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 120 246 (Polychromatic418967fa.accept_17_9_1_8_1_5045 77 120 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 120 246 2 38 60 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 120 246 3 25 40 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 120 246 2 37 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 120 246
  (Polychromatic418967fa.accept_22_7_10_4_1_2290 73 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 246 6 12 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 120 246 (Polychromatic418967fa.accept_11_5_10_4_1_1157 71 120 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 120 246 2 35 60 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 120 246 3 23 40 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 120 246 2 34 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 120 246
  (Polychromatic418967fa.accept_13_2_3_12_1_735 67 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 246 6 11 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 120 246 (Polychromatic418967fa.accept_26_13_16_12_1_14796 65 120 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 120 246 2 32 60 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 120 246 3 21 40 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 120 246 2 31 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 120 246
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 61 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 246 6 10 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 246 (Polychromatic418967fa.accept_22_15_10_4_1_10294 59 120 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 246 2 29 60 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 120 246 3 19 40 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 120 246 2 28 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 120 246
  (Polychromatic418967fa.accept_17_4_1_8_1_5070 55 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 246 6 9 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 120 246 (Polychromatic418967fa.accept_25_3_20_21_1_14795 53 120 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 246 2 26 60 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 120 246 3 17 40 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 120 246 2 25 60 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 246
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 49 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 246 6 8 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 120 246 (Polychromatic418967fa.accept_19_9_6_18_1_730 47 120 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 246 2 23 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 120 246 3 15 40 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 120 246 2 22 60 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 246
  (Polychromatic418967fa.accept_13_4_3_12_1_2066 43 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 246 6 7 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 120 246 (Polychromatic418967fa.accept_13_2_3_12_1_735 41 120 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 246 2 20 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 120 246 3 13 40 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 120 246 2 19 60 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 246
  (Polychromatic418967fa.accept_22_15_10_4_1_10294 37 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 120 246 6 6 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 120 246 (Polychromatic418967fa.accept_13_9_3_12_1_2025 35 120 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 246 2 17 60 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 120 246 3 11 40 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 120 246 2 16 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 246
  (Polychromatic418967fa.accept_19_12_6_18_1_8095 31 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 120 246 6 5 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 120 246 (Polychromatic418967fa.accept_22_7_10_4_1_2290 29 120 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 246 2 14 60 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 120 246 3 9 40 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 120 246 2 13 60 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 246
  (Polychromatic418967fa.accept_26_25_16_12_1_14794 25 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 120 246 6 4 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 120 246 (Polychromatic418967fa.accept_25_23_20_21_1_14793 23 120 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 246 2 11 60 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 120 246 3 7 40 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 120 246 2 10 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 246
  (Polychromatic418967fa.accept_25_19_20_21_1_14792 19 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 120 246 6 3 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 120 246 (Polychromatic418967fa.accept_13_4_3_12_1_2066 17 120 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 246 2 8 60 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 120 246 3 5 40 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 120 246 2 7 60 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 246
  (Polychromatic418967fa.accept_25_13_20_21_1_9709 13 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 120 246 6 2 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 120 246 (Polychromatic418967fa.accept_17_11_1_8_1_7502 11 120 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 246 2 5 60 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 120 246 3 3 40 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 120 246 2 4 60 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 246
  (Polychromatic418967fa.accept_17_7_1_8_1_6280 7 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 120 246 6 1 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 120 246 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 120 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 246 2 2 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 120 246 3 1 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 120 246 2 1 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 246 (Polychromatic418967fa.accept_19_1_6_18_1_12195
  1 120 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 246 (allA_succ_of_accept 118 119 246 (accept_3_4 118 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 117 119 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 116 119
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 119 246 (accept_3_4 115 119
  246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 119 246
  (Polychromatic418967fa.accept_9_6_2_3_1_771 114 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 119 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 113 119 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 119 246 (accept_3_4 112 119 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 119 246 (Polychromatic418967fa.accept_14_13_7_8_1_677 111 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 119 246
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 110 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 119 246 (accept_3_4 109 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 119 246 (Polychromatic418967fa.accept_13_4_2_12_1_2800 108 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 119 246 (Polychromatic418967fa.accept_9_8_2_3_1_447
  107 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 119 246 (accept_3_4
  106 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 119 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 105 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 119 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 104 119 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 119 246 (accept_3_4 103 119 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 119 246 (Polychromatic418967fa.accept_21_18_14_15_1_5809 102 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 119 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 119 246 (accept_3_4 100 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 119 246 (Polychromatic418967fa.accept_14_1_7_8_1_2063 99 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 119 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 98 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 119 246 (accept_3_4 97 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 119 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 96 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 119 246
  (Polychromatic418967fa.accept_9_5_2_3_1_194 95 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 119 246 (accept_3_4 94 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 119 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 119 246 (Polychromatic418967fa.accept_13_1_2_12_1_1299 92 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 119 246 (accept_3_4 91 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 119 246 (Polychromatic418967fa.accept_11_2_9_4_1_310 90 119
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 119 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 119 246 (accept_3_4 88 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 119 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 87 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 119 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 86 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 119 246 (accept_3_4 85 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 119 246 (Polychromatic418967fa.accept_13_6_2_12_1_2802 84 119 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 119 246
  (Polychromatic418967fa.accept_10_3_9_6_1_94 83 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 119 246 (accept_3_4 82 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 119 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 119 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 80 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 119 246 (accept_3_4 79 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 119 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 78 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 119 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 119 246 (accept_3_4 76 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 119 246 (Polychromatic418967fa.accept_10_5_9_6_1_697 75 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 119 246 (Polychromatic418967fa.accept_19_17_5_18_1_6646 74 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 119 246 (accept_3_4 73 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 119 246 (Polychromatic418967fa.accept_21_9_14_15_1_11910 72
  119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 119 246
  (Polychromatic418967fa.accept_9_8_2_3_1_447 71 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 119 246 (accept_3_4 70 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 119 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 119 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 68 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 119 246 (accept_3_4 67 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 119 246 (Polychromatic418967fa.accept_13_1_2_12_1_1299 66 119 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 119 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 119 246 (accept_3_4 64 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 119 246 (Polychromatic418967fa.accept_10_3_9_6_1_94 63 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 119 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 62 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 246 (accept_3_4 61 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 119 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 246
  (Polychromatic418967fa.accept_9_5_2_3_1_194 59 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 119 246 (accept_3_4 58 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 119 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 119 246 (Polychromatic418967fa.accept_13_4_2_12_1_2800 56 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 119 246 (accept_3_4 55 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 246 (Polychromatic418967fa.accept_15_9_14_6_1_3004 54 119
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 119 246 (accept_3_4 52 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 119 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 119 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 50 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 119 246 (accept_3_4 49 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 119 246 (Polychromatic418967fa.accept_14_6_7_8_1_624 48 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 246
  (Polychromatic418967fa.accept_16_15_7_6_1_1453 47 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 119 246 (accept_3_4 46 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 119 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 119 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 44 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 246 (accept_3_4 43 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 119 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 119 246 (accept_3_4 40 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 119 246 (Polychromatic418967fa.accept_15_9_14_6_1_3004 39 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 119 246 (Polychromatic418967fa.accept_15_8_14_6_1_3003 38 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 246 (accept_3_4 37 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 246 (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 119
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 246
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 119 246 (accept_3_4 34 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 119 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 32 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 246 (accept_3_4 31 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 246 (Polychromatic418967fa.accept_13_4_2_12_1_2800 30 119 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 119 246 (accept_3_4 28 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 119 246 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 119 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 26 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 246 (accept_3_4 25 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 246
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 246 (accept_3_4 22 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 119 246 (Polychromatic418967fa.accept_14_6_7_8_1_624 20 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 246 (accept_3_4 19 119 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 246 (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 119
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 246 (accept_3_4 16 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 119 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 246 (accept_3_4 13 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 246 (Polychromatic418967fa.accept_21_12_14_15_1_8909 12 119 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 246
  (Polychromatic418967fa.accept_23_11_4_16_1_13302 11 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 119 246 (accept_3_4 10 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 119 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 119 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 119 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 246 (accept_3_4 7 119 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 6
  119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 246 (accept_3_4 4 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 246 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 119 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 246 (Polychromatic418967fa.accept_11_2_9_4_1_310 2 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 246 (accept_3_4 1 119 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 246 (allA_succ_of_accept 117 118 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 117 118 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 118 246 2 58 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 118 246
  (Polychromatic418967fa.accept_9_7_1_3_1_443 115 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 118 246 2 57 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 118 246 (accept_3_5 113 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 118 246 2 56 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 118 246 (Polychromatic418967fa.accept_11_1_8_4_1_717 111 118 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 118 246 2 55 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 118 246
  (Polychromatic418967fa.accept_13_5_1_12_1_740 109 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 118 246 2 54 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 118 246 (accept_3_5 107 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 118 246 2 53 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 118 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 105 118 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 118 246 2 52 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 118 246
  (Polychromatic418967fa.accept_7_5_6_1_1_407 103 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 118 246 2 51 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 118 246 (accept_3_5 101 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 118 246 2 50 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 118 246 (Polychromatic418967fa.accept_12_3_10_6_1_442 99 118 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 118 246 2 49 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 118 246
  (Polychromatic418967fa.accept_9_7_1_3_1_443 97 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 118 246 2 48 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 118 246 (accept_3_5 95 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 118 246 2 47 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 118 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 118 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 118 246 2 46 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 118 246
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 91 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 118 246 2 45 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 118 246 (accept_3_5 89 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 118 246 2 44 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 118 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 87 118 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 118 246 2 43 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 118 246
  (Polychromatic418967fa.accept_9_4_1_3_1_190 85 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 118 246 2 42 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 118 246 (accept_3_5 83 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 118 246 2 41 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 118 246 (Polychromatic418967fa.accept_12_9_10_6_1_872 81 118 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 118 246 2 40 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 118 246
  (Polychromatic418967fa.accept_7_2_6_1_1_73 79 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 118 246 2 39 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 118 246 (accept_3_5 77 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 118 246 2 38 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 118 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 118 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 118 246 2 37 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 118 246
  (Polychromatic418967fa.accept_10_3_8_6_1_326 73 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 118 246 2 36 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 118 246 (accept_3_5 71 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 118 246 2 35 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 118 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 69 118 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 118 246 2 34 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 118 246
  (Polychromatic418967fa.accept_9_4_1_3_1_190 67 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 118 246 2 33 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 118 246 (accept_3_5 65 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 118 246 2 32 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 118 246 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 118 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 118 246 2 31 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 118 246
  (Polychromatic418967fa.accept_7_5_6_1_1_407 61 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 118 246 2 30 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 118 246 (accept_3_5 59 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 118 246 2 29 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 118 246 (Polychromatic418967fa.accept_12_9_10_6_1_872 57 118 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 118 246 2 28 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 118 246
  (Polychromatic418967fa.accept_19_17_4_18_1_6643 55 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 118 246 2 27 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 118 246 (accept_3_5 53 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 118 246 2 26 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 118 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 118 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 118 246 2 25 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 118 246
  (Polychromatic418967fa.accept_9_4_1_3_1_190 49 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 118 246 2 24 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 118 246 (accept_3_5 47 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 118 246 2 23 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 118 246 (Polychromatic418967fa.accept_11_1_8_4_1_717 45 118 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 246 2 22 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 246
  (Polychromatic418967fa.accept_9_7_1_3_1_443 43 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 246 2 21 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 246 (accept_3_5 41 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 246 2 20 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 246 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 118 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 246 2 19 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 246
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 246 2 18 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 246 (accept_3_5 35 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 246 2 17 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 118 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 246 2 16 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 246
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 246 2 15 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 246 (accept_3_5 29 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 246 2 14 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 246 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 118 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 246 2 13 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 246
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 246 2 12 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 246 (accept_3_5 23 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 246 2 11 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 246 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 118 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 246 2 10 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 246
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 246 2 9 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 118 246 (accept_3_5 17 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 118 246 2 8 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 118 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 118 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 118 246 2 7 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 118 246
  (Polychromatic418967fa.accept_9_4_1_3_1_190 13 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 118 246 2 6 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 118 246 (accept_3_5 11 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 118 246 2 5 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 118 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 118 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 118 246 2 4 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 118 246
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 118 246 2 3 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 118 246 (accept_3_5 5 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 118
  246 2 2 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  118 246 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 118 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 118 246 2 1 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 118 246 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 118 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 117 246 (allA_succ_of_accept 116 117 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 116 117 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 115 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 117 246 3 38 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 117 246 (Polychromatic418967fa.accept_10_3_7_6_1_659 113 117 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 117 246
  (Polychromatic418967fa.accept_12_4_9_6_1_440 112 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 111 117 246 3 37 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 110 117 246 (Polychromatic418967fa.accept_12_2_9_6_1_439 110 117 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 246
  (Polychromatic418967fa.accept_7_4_5_1_1_418 109 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 117 246 3 36 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 117 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 107 117 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 117 246
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 106 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 105 117 246 3 35 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 104 117 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 104 117 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 103 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 117 246 3 34 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 117 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 101 117 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 117 246 (Polychromatic418967fa.accept_12_4_9_6_1_440
  100 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 117 246 3 33 39 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 117 246
  (Polychromatic418967fa.accept_12_2_9_6_1_439 98 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 117 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 97 117 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 117 246 3 32 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 117 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 95
  117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 246
  (Polychromatic418967fa.accept_7_3_5_1_1_72 94 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 117 246 3 31 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 117 246 (Polychromatic418967fa.accept_12_8_9_6_1_127 92 117 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 91
  117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 117 246 3 30 39 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 117 246
  (Polychromatic418967fa.accept_18_17_9_12_1_2160 89 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 117 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 88 117 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 117 246 3 29 39 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 117 246
  (Polychromatic418967fa.accept_12_2_9_6_1_439 86 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 117 246 (Polychromatic418967fa.accept_11_8_7_4_1_3011 85 117 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 117 246 3 28 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 117 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 83
  117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 246
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 82 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 117 246 3 27 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 117 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 80 117 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 79
  117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 117 246 3 26 39 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 117 246
  (Polychromatic418967fa.accept_15_2_12_6_1_3063 77 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 76 117 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 117 246 3 25 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 117 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 74
  117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 246
  (Polychromatic418967fa.accept_7_3_5_1_1_72 73 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 117 246 3 24 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 117 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 117 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 246
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 70 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 117 246 3 23 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 117 246 (Polychromatic418967fa.accept_12_8_9_6_1_127 68 117 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 67
  117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 117 246 3 22 39 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 117 246
  (Polychromatic418967fa.accept_15_5_12_6_1_639 65 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 117 246 (Polychromatic418967fa.accept_12_4_9_6_1_440 64 117 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 117 246 3 21 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 117 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 62
  117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 246
  (Polychromatic418967fa.accept_10_1_7_6_1_91 61 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 117 246 3 20 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 117 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 117 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 246 (Polychromatic418967fa.accept_11_3_7_4_1_1133
  58 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 117 246 3 19 39 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 117 246
  (Polychromatic418967fa.accept_12_8_9_6_1_127 56 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 117 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 117 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 117 246 3 18 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 117 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 53
  117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 246
  (Polychromatic418967fa.accept_7_3_5_1_1_72 52 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 117 246 3 17 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 117 246 (Polychromatic418967fa.accept_12_2_9_6_1_439 50 117 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 246 (Polychromatic418967fa.accept_16_1_5_6_1_4435
  49 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 117 246 3 16 39 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 117 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 117 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 117 246 3 15 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 117 246 (Polychromatic418967fa.accept_12_8_9_6_1_127
  44 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 117 246 3 14 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 117 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 117 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 246 (Polychromatic418967fa.accept_12_4_9_6_1_440
  40 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 117 246 3 13 39 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 117 246
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 246 (Polychromatic418967fa.accept_15_7_12_6_1_1327 37 117 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 117 246 3 12 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 117 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 246
  (Polychromatic418967fa.accept_7_6_5_1_1_416 34 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 117 246 3 11 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 117 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 117 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 246 3 10 39 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 246
  (Polychromatic418967fa.accept_18_11_9_12_1_4427 29 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 117 246 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 117 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 117 246 3 9 39 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 117 246
  (Polychromatic418967fa.accept_12_2_9_6_1_439 26 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 117 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 246 3 8 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 246
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 117 246 3 7 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 117 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 117 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 117 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 117 246 3 6 39 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 117 246
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 246 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 117 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 246 3 5 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 246 (Polychromatic418967fa.accept_11_3_7_4_1_1133
  14 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 246
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 117 246 3 4 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 117 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 117 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 117 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 246 3 3 39 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 246
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 117 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 246 3 2 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 246 (Polychromatic418967fa.accept_15_5_12_6_1_639 5 117 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 246
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 117 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 117 246 3 1 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 117 246 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 117 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 246 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 117 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 246 (allA_succ_of_accept 115 116 246 (accept_3_4 115 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 116 246 2 57 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 116 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 113 116 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 116 246 2 56 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 116 246
  (Polychromatic418967fa.accept_12_3_8_6_1_895 111 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 116 246 2 55 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 116 246 (accept_3_4 109 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 116 246 2 54 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 116 246 (Polychromatic418967fa.accept_15_2_11_6_1_2135 107 116 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 116 246 2 53 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 116 246
  (Polychromatic418967fa.accept_9_6_8_3_1_183 105 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 116 246 2 52 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 116 246 (accept_3_4 103 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 116 246 2 51 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 116 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 101 116 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 116 246 2 50 58 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 116 246
  (Polychromatic418967fa.accept_12_3_8_6_1_895 99 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 116 246 2 49 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 116 246 (accept_3_4 97 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 116 246 2 48 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 116 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 95 116 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 116 246 2 47 58 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 116 246
  (Polychromatic418967fa.accept_12_9_8_6_1_466 93 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 116 246 2 46 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 116 246 (accept_3_4 91 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 116 246 2 45 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 116 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 89 116 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 116 246 2 44 58 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 116 246
  (Polychromatic418967fa.accept_7_3_4_1_1_71 87 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 116 246 2 43 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 116 246 (accept_3_4 85 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 116 246 2 42 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 116 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 83 116 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 116 246 2 41 58 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 116 246
  (Polychromatic418967fa.accept_12_9_8_6_1_466 81 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 116 246 2 40 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 116 246 (accept_3_4 79 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 116 246 2 39 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 116 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 77 116 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 116 246 2 38 58 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 116 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 75 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 116 246 2 37 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 116 246 (accept_3_4 73 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 116 246 2 36 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 116 246 (Polychromatic418967fa.accept_20_11_16_6_1_6121 71 116 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 116 246 2 35 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 116 246
  (Polychromatic418967fa.accept_9_6_8_3_1_183 69 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 116 246 2 34 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 116 246 (accept_3_4 67 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 116 246 2 33 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 116 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 65 116 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 116 246 2 32 58 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 116 246
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 116 246 2 31 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 116 246 (accept_3_4 61 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 116 246 2 30 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 116 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 246 2 29 58 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 246
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 57 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 246 2 28 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 246 (accept_3_4 55 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 246 2 27 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 246 (Polychromatic418967fa.accept_14_11_4_8_1_664 53 116 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 246 2 26 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 246
  (Polychromatic418967fa.accept_9_6_8_3_1_183 51 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 246 2 25 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 246 (accept_3_4 49 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 246 2 24 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 116 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 246 2 23 58 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 246
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 246 2 22 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 246 (accept_3_4 43 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 246 2 21 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 116 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 246 2 20 58 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 246
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 246 2 19 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 246 (accept_3_4 37 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 246 2 18 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 116 246 (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 116 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 246 2 17 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 116 246 2 16 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 116 246 (accept_3_4 31 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 116 246 2 15 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 116 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 116 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 246 2 14 58 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 246
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 116 246 2 13 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 116 246 (accept_3_4 25 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 116 246 2 12 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 116 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 116 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 246 2 11 58 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 246
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 246 2 10 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 116 246 (accept_3_4 19 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 116 246 2 9 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 116 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 116 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 246 2 8 58 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 246
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 116 246 2 7 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 116 246 (accept_3_4 13 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 116 246 2 6 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 116 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 116 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 116 246 2 5 58 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 116 246
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 116 246 2 4 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 116 246 (accept_3_4 7 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116
  246 2 3 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  116 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 116 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 116 246 2 2 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 116 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 116 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 246 2 1 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 246 (accept_3_4 1 116 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 246 (allA_succ_of_accept 114 115 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 114 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 246 (accept_3_5 113 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 115 246 (Polychromatic418967fa.accept_9_4_7_3_1_43 112 115
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 246
  (Polychromatic418967fa.accept_10_1_5_6_1_649 111 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 115 246 (accept_3_5 110 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 115 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 115 246 (Polychromatic418967fa.accept_13_4_11_12_1_1318 108 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 115 246 (accept_3_5 107 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 115 246 (Polychromatic418967fa.accept_15_1_10_6_1_631 106 115
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 115 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 105 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 115 246 (accept_3_5 104 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 115 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 103 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 115 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 102 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 115 246 (accept_3_5 101 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 115 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 100 115
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 115 246
  (Polychromatic418967fa.accept_10_9_5_6_1_691 99 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 115 246 (accept_3_5 98 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 115 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 115 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 96 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 115 246 (accept_3_5 95 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 115 246 (Polychromatic418967fa.accept_9_4_7_3_1_43 94 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 115 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 115 246 (accept_3_5 92 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 115 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 91 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 115 246 (Polychromatic418967fa.accept_17_5_13_8_1_7556 90 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 115 246 (accept_3_5 89 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 115 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 88 115 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 246
  (Polychromatic418967fa.accept_9_6_7_3_1_436 87 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 115 246 (accept_3_5 86 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 115 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 115 246 (Polychromatic418967fa.accept_10_4_5_6_1_651 84 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 115 246 (accept_3_5 83 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 115 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 82 115 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 115 246 (accept_3_5 80 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 115 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 79 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 115 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 78 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 115 246 (accept_3_5 77 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 115 246 (Polychromatic418967fa.accept_9_4_7_3_1_43 76 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 115 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 75 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 115 246 (accept_3_5 74 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 115 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 115 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 115 246 (accept_3_5 71 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 115 246 (Polychromatic418967fa.accept_19_13_1_18_1_5279 70 115 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 115 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 115 246 (accept_3_5 68 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 115 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 115 246 (Polychromatic418967fa.accept_13_1_11_12_1_1322 66 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 115 246 (accept_3_5 65 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 115 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 64 115 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 115 246
  (Polychromatic418967fa.accept_15_3_10_6_1_632 63 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 115 246 (accept_3_5 62 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 115 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 115 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 115 246 (accept_3_5 59 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 115 246 (accept_3_5 56 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 115 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 115 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 246 (accept_3_5 53 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 115 246 (Polychromatic418967fa.accept_16_4_3_6_1_6805 52 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 246
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 115 246 (accept_3_5 50 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 115 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 115 246 (Polychromatic418967fa.accept_15_3_10_6_1_632 48 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 246 (accept_3_5 47 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 115 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 115 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 115 246 (accept_3_5 44 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 115 246 (Polychromatic418967fa.accept_11_10_5_4_1_711 43 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 115 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 246 (accept_3_5 41 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 246
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 115 246 (accept_3_5 38 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 115 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 115 246 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 246 (accept_3_5 35 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 246 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 115
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 246 (accept_3_5 32 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 246 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 115 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 246 (accept_3_5 29 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 246
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 115 246 (accept_3_5 26 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 115 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 115 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 115 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 246 (accept_3_5 23 115 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 246 (Polychromatic418967fa.accept_9_4_7_3_1_43 22
  115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 115 246 (accept_3_5 20 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 115 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 246 (accept_3_5 17 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 246
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 115 246 (accept_3_5 14 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 246 (accept_3_5 11 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 246 (accept_3_5 8 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 246 (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 246 (accept_3_5 5 115 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 115 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 246
  (Polychromatic418967fa.accept_15_3_10_6_1_632 3 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 246 (accept_3_5 2 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 115 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 246 (allA_succ_of_accept 113 114 246 (Polychromatic418967fa.accept_9_5_6_3_1_40 113 114 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 114 246 2 56 57 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 111 114 246 3 37 38 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 110 114 246 2 55 57 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 114 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 109 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 114 246 6 18 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 114 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 107 114 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 114 246 2 53 57 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 114 246 3 35 38 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 114 246 2 52 57 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 114 246
  (Polychromatic418967fa.accept_9_4_6_3_1_179 103 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 114 246 6 17 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 114 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 101 114 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 114 246 2 50 57 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 114 246 3 33 38 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 114 246 2 49 57 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 114 246
  (Polychromatic418967fa.accept_7_6_2_1_1_214 97 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 114 246 6 16 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 114 246 (Polychromatic418967fa.accept_9_5_6_3_1_40 95 114 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 114 246 2 47 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 114 246 3 31 38 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 114 246 2 46 57 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 114 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 91 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 246 6 15 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 89 114 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 114 246 2 44 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 114 246 3 29 38 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 114 246 2 43 57 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 114 246
  (Polychromatic418967fa.accept_9_4_6_3_1_179 85 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 246 6 14 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 114 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 114 246 2 41 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 114 246 3 27 38 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 114 246 2 40 57 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 114 246
  (Polychromatic418967fa.accept_9_7_6_3_1_456 79 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 246 6 13 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 246 (Polychromatic418967fa.accept_9_5_6_3_1_40 77 114 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 114 246 2 38 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 114 246 3 25 38 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 114 246 2 37 57 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 114 246
  (Polychromatic418967fa.accept_7_3_2_1_1_225 73 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 246 6 12 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 71 114 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 114 246 2 35 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 114 246 3 23 38 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 114 246 2 34 57 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 114 246
  (Polychromatic418967fa.accept_9_4_6_3_1_179 67 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 246 6 11 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 65 114 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 246 2 32 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 114 246 3 21 38 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 114 246 2 31 57 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 114 246
  (Polychromatic418967fa.accept_9_7_6_3_1_456 61 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 246 6 10 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 114 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 246 2 29 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 114 246 3 19 38 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 114 246 2 28 57 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 246
  (Polychromatic418967fa.accept_7_6_2_1_1_214 55 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 246 6 9 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 114 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 53 114 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 246 2 26 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 114 246 3 17 38 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 114 246 2 25 57 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 246
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 246 6 8 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 114 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 114 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 246 2 23 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 114 246 3 15 38 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 114 246 2 22 57 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 246
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 246 6 7 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 114 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 114 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 246 2 20 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 114 246 3 13 38 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 114 246 2 19 57 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 246 6 6 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 114 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 114 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 246 2 17 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 114 246 3 11 38 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 114 246 2 16 57 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 246
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 246 6 5 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 114 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 114 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 246 2 14 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 114 246 3 9 38 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 114 246 2 13 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 246
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 246 6 4 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 114 246 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 114 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 246 2 11 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 114 246 3 7 38 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 114 246 2 10 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 246 6 3 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 114 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 246 2 8 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 114 246 3 5 38 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 114 246 2 7 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 246
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 246 6 2 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 114 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 114 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 246 2 5 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 114 246 3 3 38 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 114 246 2 4 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 246 (Polychromatic418967fa.accept_9_7_6_3_1_456 7
  114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 246 6 1 19 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 114 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 114 246 2 2 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 114 246 3 1 38 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 114 246 2 1 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 114 246 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 114 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 114
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 246 (allA_succ_of_accept 112 113 246 (accept_3_4 112 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 113 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 110 113
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 246 (accept_3_4 109 113
  246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 246
  (Polychromatic418967fa.accept_10_8_3_6_1_685 108 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 107 113 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 246 (accept_3_4 106 113 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 113 246 (Polychromatic418967fa.accept_9_6_5_3_1_205 105 113 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 246
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 104 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 113 246 (accept_3_4 103 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 113 246 (Polychromatic418967fa.accept_21_18_8_15_1_5745 102 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 113 246 (Polychromatic418967fa.accept_9_2_5_3_1_37
  101 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 246 (accept_3_4
  100 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 113 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 98 113 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 113 246 (accept_3_4 97 113 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 113 246 (Polychromatic418967fa.accept_9_6_5_3_1_205 96 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 113 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 95
  113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 246 (accept_3_4 94
  113 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 246
  (Polychromatic418967fa.accept_14_9_1_8_1_2849 93 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 113 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 92 113 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 113 246 (accept_3_4 91 113 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 113 246 (Polychromatic418967fa.accept_21_6_8_15_1_8903 90 113 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 113 246
  (Polychromatic418967fa.accept_9_8_5_3_1_777 89 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 113 246 (accept_3_4 88 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 113 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 113 246 (Polychromatic418967fa.accept_13_8_9_12_1_2813 86 113 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 113 246 (accept_3_4 85 113 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 113 246 (Polychromatic418967fa.accept_11_7_3_4_1_729 84 113
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 113 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 113 246 (accept_3_4 82 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 113 246 (Polychromatic418967fa.accept_13_3_9_12_1_2062 81 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 113 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 80 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 113 246 (accept_3_4 79 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 113 246 (Polychromatic418967fa.accept_9_6_5_3_1_205 78 113 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 113 246
  (Polychromatic418967fa.accept_10_7_3_6_1_644 77 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 113 246 (accept_3_4 76 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 113 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 113 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 74 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 113 246 (accept_3_4 73 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 113 246 (Polychromatic418967fa.accept_14_2_1_8_1_650 72 113 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 113 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 113 246 (accept_3_4 70 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 113 246 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 113 246 (Polychromatic418967fa.accept_10_8_3_6_1_685 68 113 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 113 246 (accept_3_4 67 113 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 113 246 (Polychromatic418967fa.accept_16_2_1_6_1_2342 66 113
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 113 246
  (Polychromatic418967fa.accept_9_2_5_3_1_37 65 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 113 246 (accept_3_4 64 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 113 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 113 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 62 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 246 (accept_3_4 61 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 113 246 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 113 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 113 246 (accept_3_4 58 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 113 246 (Polychromatic418967fa.accept_10_7_3_6_1_644 57 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 113 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 56 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 246 (accept_3_4 55 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 246 (Polychromatic418967fa.accept_21_12_8_15_1_8955 54 113 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 246
  (Polychromatic418967fa.accept_9_8_5_3_1_777 53 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 113 246 (accept_3_4 52 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 113 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 246 (Polychromatic418967fa.accept_16_2_1_6_1_2342 50 113 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 246 (accept_3_4 49 113 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 246 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 113
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 246 (accept_3_4 46 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 246 (Polychromatic418967fa.accept_18_9_5_12_1_9813 45 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 44 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 246 (accept_3_4 43 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 246 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 113 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 246
  (Polychromatic418967fa.accept_22_19_3_4_1_10173 41 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 113 246 (accept_3_4 40 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 113 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 113 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 38 113 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 246 (accept_3_4 37 113 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 246
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 246 (accept_3_4 34 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 246 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 113 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 246
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 32 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 246 (accept_3_4 31 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 246 (Polychromatic418967fa.accept_14_2_1_8_1_650 30 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 246 (accept_3_4 28 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 113 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 246
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 246 (accept_3_4 25 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 246 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 246 (accept_3_4 22 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 246 (Polychromatic418967fa.accept_13_8_9_12_1_2813 21 113 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 246
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 246 (accept_3_4 19 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 246 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 246 (accept_3_4 16 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 113 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 246
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 14 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 246 (accept_3_4 13 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 246 (Polychromatic418967fa.accept_21_12_8_15_1_8955 12 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 246 (accept_3_4 10 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 246 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 113 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 246
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 246 (accept_3_4 7 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 246 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 246 (Polychromatic418967fa.accept_16_5_1_6_1_3367 5 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 246 (accept_3_4 4 113 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 113 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 246
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 246 (accept_3_4 1 113 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 246 (allA_succ_of_accept 111 112 246 (Polychromatic418967fa.accept_10_1_2_6_1_638 111 112 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 112 246 2 55 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 112 246
  (Polychromatic418967fa.accept_9_1_4_3_1_201 109 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 112 246 2 54 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 112 246 (accept_3_5 107 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 112 246 2 53 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 112 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 105 112 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 112 246 2 52 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 112 246
  (Polychromatic418967fa.accept_15_13_7_6_1_682 103 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 112 246 2 51 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 112 246 (accept_3_5 101 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 112 246 2 50 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 112 246 (Polychromatic418967fa.accept_12_3_4_6_1_434 99 112 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 112 246 2 49 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 112 246
  (Polychromatic418967fa.accept_9_7_4_3_1_204 97 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 112 246 2 48 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 112 246 (accept_3_5 95 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 112 246 2 47 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 112 246 (Polychromatic418967fa.accept_12_9_4_6_1_460 93 112 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 112 246 2 46 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 112 246
  (Polychromatic418967fa.accept_9_1_4_3_1_201 91 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 112 246 2 45 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 112 246 (accept_3_5 89 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 112 246 2 44 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 112 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 87 112 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 112 246 2 43 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 112 246
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 85 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 112 246 2 42 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 112 246 (accept_3_5 83 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 112 246 2 41 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 112 246 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 112 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 112 246 2 40 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 112 246
  (Polychromatic418967fa.accept_9_7_4_3_1_204 79 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 112 246 2 39 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 112 246 (accept_3_5 77 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 112 246 2 38 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 112 246 (Polychromatic418967fa.accept_11_9_2_4_1_707 75 112 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 112 246 2 37 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 112 246
  (Polychromatic418967fa.accept_9_1_4_3_1_201 73 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 112 246 2 36 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 112 246 (accept_3_5 71 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 112 246 2 35 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 112 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 69 112 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 112 246 2 34 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 112 246
  (Polychromatic418967fa.accept_19_10_17_18_1_9555 67 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 112 246 2 33 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 112 246 (accept_3_5 65 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 112 246 2 32 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 112 246 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 112 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 112 246 2 31 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 112 246
  (Polychromatic418967fa.accept_9_7_4_3_1_204 61 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 112 246 2 30 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 112 246 (accept_3_5 59 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 112 246 2 29 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 112 246 (Polychromatic418967fa.accept_12_9_4_6_1_460 57 112 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 112 246 2 28 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 112 246
  (Polychromatic418967fa.accept_9_1_4_3_1_201 55 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 112 246 2 27 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 112 246 (accept_3_5 53 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 112 246 2 26 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 112 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 112 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 112 246 2 25 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 112 246
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 49 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 112 246 2 24 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 112 246 (accept_3_5 47 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 112 246 2 23 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 112 246 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 112 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 112 246 2 22 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 112 246
  (Polychromatic418967fa.accept_9_7_4_3_1_204 43 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 112 246 2 21 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 112 246 (accept_3_5 41 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 112 246 2 20 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 112 246 (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 112 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 112 246 2 19 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 112 246
  (Polychromatic418967fa.accept_9_1_4_3_1_201 37 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 112 246 2 18 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 112 246 (accept_3_5 35 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 112 246 2 17 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 112 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 112 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 112 246 2 16 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 112 246
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 112 246 2 15 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 112 246 (accept_3_5 29 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 112 246 2 14 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 112 246 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 112 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 246 2 13 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 246
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 246 2 12 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 112 246 (accept_3_5 23 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 112 246 2 11 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 112 246 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 112 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 246 2 10 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 246
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 246 2 9 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 112 246 (accept_3_5 17 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 112 246 2 8 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 112 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 112 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 112 246 2 7 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 112 246
  (Polychromatic418967fa.accept_15_13_7_6_1_682 13 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 112 246 2 6 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 112 246 (accept_3_5 11 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 112 246 2 5 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 112 246 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 112 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 112 246 2 4 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 112 246
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 112 246 2 3 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 112 246 (accept_3_5 5 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112
  246 2 2 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  112 246 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 112 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 112 246 2 1 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 112 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 112 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 246 (allA_succ_of_accept 110 111 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 110 111 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 109 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 111 246 3 36 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 111 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 107 111 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 111 246
  (Polychromatic418967fa.accept_12_10_3_6_1_882 106 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 111 246 3 35 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 111 246 (Polychromatic418967fa.accept_12_8_3_6_1_909 104 111 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 246
  (Polychromatic418967fa.accept_7_5_6_1_1_407 103 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 111 246 3 34 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 111 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 101 111 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 111 246 (Polychromatic418967fa.accept_7_2_6_1_1_73
  100 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 111 246 3 33 37 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 111 246
  (Polychromatic418967fa.accept_12_2_3_6_1_112 98 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 111 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 111 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 111 246 3 32 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 111 246 (Polychromatic418967fa.accept_10_5_1_6_1_672
  95 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 111 246
  (Polychromatic418967fa.accept_12_10_3_6_1_882 94 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 111 246 3 31 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 111 246 (Polychromatic418967fa.accept_10_2_1_6_1_634 92 111 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 246
  (Polychromatic418967fa.accept_14_7_13_8_1_2067 91 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 111 246 3 30 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 111 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 89 111 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 111 246 (Polychromatic418967fa.accept_12_4_3_6_1_879
  88 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 111 246 3 29 37 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 111 246
  (Polychromatic418967fa.accept_7_2_6_1_1_73 86 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 111 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 111 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 111 246 3 28 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 111 246 (Polychromatic418967fa.accept_13_5_7_12_1_2757
  83 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 111 246
  (Polychromatic418967fa.accept_7_5_6_1_1_407 82 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 111 246 3 27 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 111 246 (Polychromatic418967fa.accept_12_8_3_6_1_909 80 111 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 79
  111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 111 246 3 26 37 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 111 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 246 (Polychromatic418967fa.accept_12_4_3_6_1_879 76 111 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 111 246 3 25 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 111 246 (Polychromatic418967fa.accept_11_8_1_4_1_2318
  74 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 73 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 111 246 3 24 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 111 246 (Polychromatic418967fa.accept_13_6_7_12_1_3504 71 111 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 246
  (Polychromatic418967fa.accept_12_10_3_6_1_882 70 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 111 246 3 23 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 111 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 111 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 246 (Polychromatic418967fa.accept_10_7_1_6_1_673
  67 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 111 246 3 22 37 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 111 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 246 (Polychromatic418967fa.accept_12_4_3_6_1_879 64 111 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 111 246 3 21 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 111 246 (Polychromatic418967fa.accept_10_2_1_6_1_634
  62 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 61 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 111 246 3 20 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 111 246 (Polychromatic418967fa.accept_19_2_16_18_1_10922 59 111 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 246
  (Polychromatic418967fa.accept_7_2_6_1_1_73 58 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 111 246 3 19 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 111 246 (Polychromatic418967fa.accept_12_8_3_6_1_909 56 111 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 246 (Polychromatic418967fa.accept_10_5_1_6_1_672
  55 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 111 246 3 18 37 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 111 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 246 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 111 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 111 246 3 17 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 111 246 (Polychromatic418967fa.accept_12_2_3_6_1_112
  50 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 111 246 3 16 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 111 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 111 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 246 (Polychromatic418967fa.accept_12_10_3_6_1_882
  46 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 111 246 3 15 37 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 111 246
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 111 246 (Polychromatic418967fa.accept_13_4_7_12_1_2823 43 111 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 111 246 3 14 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 111 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 41
  111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 246
  (Polychromatic418967fa.accept_7_5_6_1_1_407 40 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 111 246 3 13 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 111 246 (Polychromatic418967fa.accept_12_2_3_6_1_112 38 111 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 111 246 3 12 37 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 111 246
  (Polychromatic418967fa.accept_10_5_1_6_1_672 35 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 246 (Polychromatic418967fa.accept_12_10_3_6_1_882 34 111 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 111 246 3 11 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 111 246 (Polychromatic418967fa.accept_10_2_1_6_1_634
  32 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 246
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 31 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 111 246 3 10 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 111 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 111 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 246 (Polychromatic418967fa.accept_12_4_3_6_1_879
  28 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 111 246 3 9 37 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 111 246
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 111 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 246 3 8 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 23
  111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 246
  (Polychromatic418967fa.accept_10_2_1_6_1_634 22 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 111 246 3 7 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 111 246 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 111 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 111 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 111 246 3 6 37 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 111 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 111 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 246 3 5 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 246 (Polychromatic418967fa.accept_12_2_3_6_1_112
  14 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 111 246 3 4 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 111 246 (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 111 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 246 (Polychromatic418967fa.accept_12_10_3_6_1_882
  10 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 246 3 3 37 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 246
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 8 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 246 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 111 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 246 3 2 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 111 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 246
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 111 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 111 246 3 1 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 111 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 111 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 246 (allA_succ_of_accept 109 110 246 (accept_3_4 109 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 110 246 2 54 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 110 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 107 110 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 110 246 2 53 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 110 246
  (Polychromatic418967fa.accept_9_6_2_3_1_771 105 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 110 246 2 52 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 110 246 (accept_3_4 103 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 110 246 2 51 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 110 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 101 110 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 110 246 2 50 55 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 110 246
  (Polychromatic418967fa.accept_12_3_2_6_1_138 99 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 110 246 2 49 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 110 246 (accept_3_4 97 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 110 246 2 48 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 110 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 95 110 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 110 246 2 47 55 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 110 246
  (Polychromatic418967fa.accept_12_9_2_6_1_455 93 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 110 246 2 46 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 110 246 (accept_3_4 91 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 110 246 2 45 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 110 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 89 110 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 110 246 2 44 55 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 110 246
  (Polychromatic418967fa.accept_7_3_5_1_1_72 87 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 110 246 2 43 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 110 246 (accept_3_4 85 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 110 246 2 42 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 110 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 110 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 110 246 2 41 55 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 110 246
  (Polychromatic418967fa.accept_7_4_5_1_1_418 81 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 110 246 2 40 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 110 246 (accept_3_4 79 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 110 246 2 39 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 110 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 77 110 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 110 246 2 38 55 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 110 246
  (Polychromatic418967fa.accept_12_3_2_6_1_138 75 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 110 246 2 37 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 110 246 (accept_3_4 73 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 110 246 2 36 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 110 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 71 110 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 110 246 2 35 55 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 110 246
  (Polychromatic418967fa.accept_7_6_5_1_1_416 69 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 110 246 2 34 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 110 246 (accept_3_4 67 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 110 246 2 33 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 110 246 (Polychromatic418967fa.accept_20_5_10_6_1_6166 65 110 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 110 246 2 32 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 246
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 110 246 2 31 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 110 246 (accept_3_4 61 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 246 2 30 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 110 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 246 2 29 55 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 246
  (Polychromatic418967fa.accept_12_9_2_6_1_455 57 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 246 2 28 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 110 246 (accept_3_4 55 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 110 246 2 27 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 110 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 110 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 246 2 26 55 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 246
  (Polychromatic418967fa.accept_9_6_2_3_1_771 51 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 246 2 25 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 246 (accept_3_4 49 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 246 2 24 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 246 (Polychromatic418967fa.accept_19_9_15_18_1_10919 47 110 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 246 2 23 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 246
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 110 246 2 22 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 110 246 (accept_3_4 43 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 246 2 21 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 110 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 246 2 20 55 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 246
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 246 2 19 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 246 (accept_3_4 37 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 246 2 18 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 110 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 246 2 17 55 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 246
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 246 2 16 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 246 (accept_3_4 31 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 246 2 15 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 246 (Polychromatic418967fa.accept_15_14_5_6_1_6168 29 110 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 246 2 14 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 246
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 246 2 13 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 246 (accept_3_4 25 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 246 2 12 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 110 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 246 2 11 55 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 246
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 246 2 10 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 246 (accept_3_4 19 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 246 2 9 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 110 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 110 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 246 2 8 55 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 246
  (Polychromatic418967fa.accept_9_6_2_3_1_771 15 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 110 246 2 7 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 110 246 (accept_3_4 13 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 110 246 2 6 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 110 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 110 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 246 2 5 55 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 246
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 246 2 4 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 246 (accept_3_4 7 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  246 2 3 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  110 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 110 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 110 246 2 2 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 110 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 110 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 246 2 1 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 246 (accept_3_4 1 110 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 246 (allA_succ_of_accept 108 109 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 108 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 246 (accept_3_5 107 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 109 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 106 109
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 246
  (Polychromatic418967fa.accept_9_6_1_3_1_191 105 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 246 (accept_3_5 104 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 109 246 (Polychromatic418967fa.accept_14_4_11_8_1_2034 102 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 246 (accept_3_5 101 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 246 (Polychromatic418967fa.accept_15_10_4_6_1_2129 100
  109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 246 (accept_3_5 98 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 97 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 96 109 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 246 (accept_3_5 95 109 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 94 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 246
  (Polychromatic418967fa.accept_10_3_9_6_1_94 93 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 246 (accept_3_5 92 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 109 246 (Polychromatic418967fa.accept_20_10_9_6_1_6164 90 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 246 (accept_3_5 89 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 88 109 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 109 246 (accept_3_5 86 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 109 246 (Polychromatic418967fa.accept_9_4_1_3_1_190 85 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 109 246 (Polychromatic418967fa.accept_13_6_5_12_1_307 84 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 246 (accept_3_5 83 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 82 109 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 246
  (Polychromatic418967fa.accept_22_15_21_4_1_5310 81 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 109 246 (accept_3_5 80 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 109 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 109 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 109 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 78 109 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 246 (accept_3_5 77 109 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 246 (Polychromatic418967fa.accept_9_4_1_3_1_190
  76 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 246 (accept_3_5 74 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 73 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 109 246 (Polychromatic418967fa.accept_13_7_5_12_1_1305 72 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 246 (accept_3_5 71 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 70 109 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 246
  (Polychromatic418967fa.accept_9_6_1_3_1_191 69 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 246 (accept_3_5 68 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 109 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 246 (accept_3_5 65 109 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 246 (Polychromatic418967fa.accept_19_7_14_18_1_6654 64 109 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 246 (accept_3_5 62 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 60 109 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 246 (accept_3_5 59 109 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 246 (Polychromatic418967fa.accept_9_4_1_3_1_190 58 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 246
  (Polychromatic418967fa.accept_16_9_13_6_1_2334 57 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 246 (accept_3_5 56 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 109 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 246 (accept_3_5 53 109 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 246 (accept_3_5 50 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 246 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 246 (Polychromatic418967fa.accept_17_14_7_8_1_7544 48 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 246 (accept_3_5 47 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 246 (Polychromatic418967fa.accept_13_7_5_12_1_1305 46 109
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 246
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 246 (accept_3_5 44 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 109 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 246 (accept_3_5 41 109 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 246 (accept_3_5 38 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 246 (Polychromatic418967fa.accept_20_17_9_6_1_6219 37 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 246 (Polychromatic418967fa.accept_16_4_13_6_1_4417 36 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 246 (accept_3_5 35 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 109 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 246 (accept_3_5 32 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 246 (Polychromatic418967fa.accept_13_4_5_12_1_751 30 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 246 (accept_3_5 29 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 246 (Polychromatic418967fa.accept_13_2_5_12_1_2043 28 109
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 246 (accept_3_5 26 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 109 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 246 (accept_3_5 23 109 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 246 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 246
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 21 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 246 (accept_3_5 20 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 246 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 246 (accept_3_5 17 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 109 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 246 (accept_3_5 14 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 246 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 109 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 246 (accept_3_5 11 109 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 246
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 246 (accept_3_5 8 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 109 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 246 (accept_3_5 5 109 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 246 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 109 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 246 (accept_3_5 2 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 246 (Polychromatic418967fa.accept_13_1_5_12_1_306 1 109 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 246 (allA_succ_of_accept 107 108 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 107 108 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 108 246 2 53 54 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 108 246 3 35 36 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 108 246 2 52 54 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 108 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 103 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 108 246 6 17 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 108 246 (Polychromatic418967fa.accept_11_2_9_4_1_310 101 108 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 108 246 2 50 54 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 108 246 3 33 36 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 108 246 2 49 54 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 108 246
  (Polychromatic418967fa.accept_22_9_20_4_1_5309 97 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 246 6 16 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 108 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 95 108 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 108 246 2 47 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 108 246 3 31 36 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 108 246 2 46 54 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 108 246
  (Polychromatic418967fa.accept_15_1_3_6_1_621 91 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 108 246 6 15 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 108 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 108 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 108 246 2 44 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 108 246 3 29 36 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 108 246 2 43 54 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 108 246
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 85 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 246 6 14 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 246 (Polychromatic418967fa.accept_10_3_8_6_1_326 83 108 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 108 246 2 41 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 108 246 3 27 36 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 108 246 2 40 54 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 108 246
  (Polychromatic418967fa.accept_7_2_3_1_1_10 79 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 246 6 13 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 246 (Polychromatic418967fa.accept_17_9_6_8_1_6315 77 108 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 108 246 2 38 54 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 108 246 3 25 36 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 108 246 2 37 54 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 108 246
  (Polychromatic418967fa.accept_10_3_8_6_1_326 73 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 246 6 12 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 246 (Polychromatic418967fa.accept_15_11_3_6_1_1306 71 108 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 246 2 35 54 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 108 246 3 23 36 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 108 246 2 34 54 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 246
  (Polychromatic418967fa.accept_7_4_3_1_1_87 67 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 246 6 11 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 108 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 246 2 32 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 108 246 3 21 36 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 108 246 2 31 54 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 61 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 246 6 10 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 246 (Polychromatic418967fa.accept_13_7_4_12_1_1341 59 108 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 246 2 29 54 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 108 246 3 19 36 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 108 246 2 28 54 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 246
  (Polychromatic418967fa.accept_13_3_4_12_1_36 55 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 246 6 9 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 108 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 108 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 246 2 26 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 108 246 3 17 36 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 108 246 2 25 54 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 246
  (Polychromatic418967fa.accept_17_15_6_8_1_6343 49 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 246 6 8 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 108 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 108 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 246 2 23 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 108 246 3 15 36 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 108 246 2 22 54 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 246
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 246 6 7 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 108 246 (Polychromatic418967fa.accept_13_2_4_12_1_745 41 108 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 246 2 20 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 108 246 3 13 36 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 108 246 2 19 54 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 246
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 246 6 6 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 246 (Polychromatic418967fa.accept_11_2_9_4_1_310 35 108 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 246 2 17 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 108 246 3 11 36 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 108 246 2 16 54 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 246
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 31 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 246 6 5 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 108 246 (Polychromatic418967fa.accept_13_3_4_12_1_36 29 108 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 246 2 14 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 108 246 3 9 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 108 246 2 13 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 246
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 246 6 4 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 108 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 108 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 246 2 11 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 108 246 3 7 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 108 246 2 10 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 246 6 3 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 246 (Polychromatic418967fa.accept_19_17_13_18_1_9542 17 108 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 246 2 8 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 108 246 3 5 36 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 108 246 2 7 54 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 246
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 246 6 2 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 108 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 108 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 246 2 5 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 108 246 3 3 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 108 246 2 4 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 246 (Polychromatic418967fa.accept_13_7_4_12_1_1341
  7 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 246 6 1 18 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 108 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 108 246 2 2 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 108 246 3 1 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 108 246 2 1 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 246 (Polychromatic418967fa.accept_15_1_3_6_1_621 1 108 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 246 (allA_succ_of_accept 106 107 246 (accept_3_4 106 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 107 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 104 107
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 246 (accept_3_4 103 107
  246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 246
  (Polychromatic418967fa.accept_15_12_2_6_1_2127 102 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 107 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 101 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 246 (accept_3_4 100 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 107 246 (Polychromatic418967fa.accept_14_1_9_8_1_2863 99 107 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 246
  (Polychromatic418967fa.accept_15_8_2_6_1_2125 98 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 107 246 (accept_3_4 97 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 107 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 96 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 107 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 95 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 246 (accept_3_4 94 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 107 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 107 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 246
  (Polychromatic418967fa.accept_9_2_8_3_1_181 92 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 246 (accept_3_4 91 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 90 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 107 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 89 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 246 (accept_3_4 88 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 107 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 246
  (Polychromatic418967fa.accept_9_5_8_3_1_437 86 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 246 (accept_3_4 85 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 246 (Polychromatic418967fa.accept_11_7_8_4_1_718 84 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 246 (accept_3_4 82 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 107 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 246
  (Polychromatic418967fa.accept_7_3_2_1_1_225 80 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 246 (accept_3_4 79 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 78 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 246 (accept_3_4 76 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 246 (Polychromatic418967fa.accept_30_15_17_6_1_12782 75 107 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 246
  (Polychromatic418967fa.accept_9_2_8_3_1_181 74 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 246 (accept_3_4 73 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 246 (Polychromatic418967fa.accept_15_12_2_6_1_2127 72 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 246 (Polychromatic418967fa.accept_10_1_7_6_1_91 71 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 246 (accept_3_4 70 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 107 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 246
  (Polychromatic418967fa.accept_9_5_8_3_1_437 68 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 246 (accept_3_4 67 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 246 (accept_3_4 64 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 246 (Polychromatic418967fa.accept_10_3_7_6_1_659 63 107 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 246
  (Polychromatic418967fa.accept_7_6_2_1_1_214 62 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 246 (accept_3_4 61 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 246 (accept_3_4 58 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 107 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 246
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 246 (accept_3_4 55 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 246 (Polychromatic418967fa.accept_13_2_3_12_1_735 54 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 246 (accept_3_4 52 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 107 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 246
  (Polychromatic418967fa.accept_9_5_8_3_1_437 50 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 246 (accept_3_4 49 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 246 (accept_3_4 46 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 107 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 246
  (Polychromatic418967fa.accept_19_6_12_18_1_8141 44 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 107 246 (accept_3_4 43 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 107 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 107 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 107 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 246 (accept_3_4 40 107 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 246
  (Polychromatic418967fa.accept_19_1_12_18_1_10820 39 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 246 (accept_3_4 37 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 246 (Polychromatic418967fa.accept_16_4_11_6_1_5591 36 107 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 246
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 35 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 246 (accept_3_4 34 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 32 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 246 (accept_3_4 31 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 246 (Polychromatic418967fa.accept_13_4_3_12_1_2066 30 107 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 246 (accept_3_4 28 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 246 (Polychromatic418967fa.accept_15_11_2_6_1_3010 26 107 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 246 (accept_3_4 25 107 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 107 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 246
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 246 (accept_3_4 22 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 246 (accept_3_4 19 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 246 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 107 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 246 (accept_3_4 16 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 246 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 246 (accept_3_4 13 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 246 (Polychromatic418967fa.accept_11_1_8_4_1_717 12 107 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 246
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 246 (accept_3_4 10 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 246 (Polychromatic418967fa.accept_15_8_2_6_1_2125 8 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 246 (accept_3_4 7 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 107 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 246 (accept_3_4 4 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 107 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 246 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 246 (accept_3_4 1 107 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 246 (allA_succ_of_accept 105 106 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 105 106 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 106 246 2 52 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 106 246
  (Polychromatic418967fa.accept_9_4_7_3_1_43 103 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 106 246 2 51 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 106 246 (accept_3_5 101 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 106 246 2 50 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 106 246 (Polychromatic418967fa.accept_12_3_10_6_1_442 99 106 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 106 246 2 49 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 106 246
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 97 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 106 246 2 48 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 106 246 (accept_3_5 95 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 106 246 2 47 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 106 246 (Polychromatic418967fa.accept_12_9_10_6_1_872 93 106 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 106 246 2 46 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 106 246
  (Polychromatic418967fa.accept_9_1_7_3_1_41 91 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 106 246 2 45 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 106 246 (accept_3_5 89 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 106 246 2 44 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 106 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 87 106 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 106 246 2 43 53 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 106 246
  (Polychromatic418967fa.accept_9_4_7_3_1_43 85 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 106 246 2 42 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 106 246 (accept_3_5 83 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 106 246 2 41 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 106 246 (Polychromatic418967fa.accept_12_9_10_6_1_872 81 106 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 106 246 2 40 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 106 246
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 79 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 106 246 2 39 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 106 246 (accept_3_5 77 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 106 246 2 38 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 106 246 (Polychromatic418967fa.accept_12_3_10_6_1_442 75 106 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 106 246 2 37 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 106 246
  (Polychromatic418967fa.accept_9_1_7_3_1_41 73 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 106 246 2 36 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 106 246 (accept_3_5 71 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 106 246 2 35 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 106 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 69 106 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 106 246 2 34 53 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 106 246
  (Polychromatic418967fa.accept_9_4_7_3_1_43 67 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 106 246 2 33 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 106 246 (accept_3_5 65 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 106 246 2 32 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 106 246 (Polychromatic418967fa.accept_11_8_7_4_1_3011 63 106 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 246 2 31 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 246
  (Polychromatic418967fa.accept_19_4_11_18_1_3909 61 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 106 246 2 30 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 106 246 (accept_3_5 59 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 246 2 29 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 246 (Polychromatic418967fa.accept_12_9_10_6_1_872 57 106 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 246 2 28 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 246
  (Polychromatic418967fa.accept_9_1_7_3_1_41 55 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 106 246 2 27 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 246 (accept_3_5 53 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 246 2 26 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 106 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 246 2 25 53 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 246
  (Polychromatic418967fa.accept_9_4_7_3_1_43 49 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 246 2 24 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 246 (accept_3_5 47 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 246 2 23 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 246 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 106 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 246 2 22 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 246
  (Polychromatic418967fa.accept_13_4_2_12_1_2800 43 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 246 2 21 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 246 (accept_3_5 41 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 246 2 20 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 246 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 106 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 246 2 19 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 246
  (Polychromatic418967fa.accept_9_1_7_3_1_41 37 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 246 2 18 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 246 (accept_3_5 35 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 246 2 17 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 106 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 246 2 16 53 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 246
  (Polychromatic418967fa.accept_9_4_7_3_1_43 31 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 246 2 15 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 246 (accept_3_5 29 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 246 2 14 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 246 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 106 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 246 2 13 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 246
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 25 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 246 2 12 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 246 (accept_3_5 23 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 246 2 11 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 246 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 106 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 246 2 10 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 246
  (Polychromatic418967fa.accept_9_1_7_3_1_41 19 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 246 2 9 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 106 246 (accept_3_5 17 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 106 246 2 8 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 106 246 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 106 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 106 246 2 7 53 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 106 246
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 106 246 2 6 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 106 246 (accept_3_5 11 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 106 246 2 5 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 106 246 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 106 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 106 246 2 4 53 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 106 246
  (Polychromatic418967fa.accept_15_7_1_6_1_6150 7 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 106 246 2 3 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 106 246 (accept_3_5 5 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 106
  246 2 2 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  106 246 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 106 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 106 246 2 1 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 106 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 106 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 246 (allA_succ_of_accept 104 105 246 (Polychromatic418967fa.accept_9_5_6_3_1_40 104 105 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 103 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 105 246 3 34 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 105 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 101 105 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 105 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 100 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 105 246 3 33 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 105 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 98 105 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 246 (Polychromatic418967fa.accept_9_7_6_3_1_456
  97 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 105 246 3 32 35 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 105 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 94 105 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 105 246 3 31 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 105 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 92
  105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 91 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 105 246 3 30 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 105 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 89 105 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 246 (Polychromatic418967fa.accept_9_7_6_3_1_456
  88 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 105 246 3 29 35 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 105 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 86 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 105 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 85 105 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 105 246 3 28 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 105 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 83
  105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 105 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 82 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 105 246 3 27 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 105 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 80 105 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 79
  105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 105 246 3 26 35 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 105 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 77 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 76 105 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 105 246 3 25 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 105 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 74
  105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 73 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 105 246 3 24 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 105 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 105 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 105 246 (Polychromatic418967fa.accept_9_7_6_3_1_456
  70 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 105 246 3 23 35 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 105 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 68 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 105 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 105 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 105 246 3 22 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 105 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 65
  105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 64 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 105 246 3 21 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 105 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 62 105 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 246 (Polychromatic418967fa.accept_9_7_6_3_1_456
  61 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 246 3 20 35 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 58 105 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 105 246 3 19 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 105 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 56
  105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 105 246 3 18 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 105 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 53 105 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 246 (Polychromatic418967fa.accept_9_7_6_3_1_456
  52 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 105 246 3 17 35 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 105 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 50 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 105 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 105 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 105 246 3 16 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 105 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 46 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 105 246 3 15 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 105 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 44 105 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 105 246 3 14 35 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 105 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 41 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 105 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 105 246 3 13 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 105 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 38
  105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 105 246 3 12 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 105 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 105 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 246 (Polychromatic418967fa.accept_9_7_6_3_1_456
  34 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 105 246 3 11 35 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 105 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 32 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 105 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 246 3 10 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 105 246 3 9 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 105 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 105 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 246 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 105 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 105 246 3 8 35 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 105 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 105 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 246 3 7 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 105 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 20
  105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 105 246 3 6 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 105 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 105 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 246 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 105 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 246 3 5 35 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 105 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 246 3 4 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 105 246 3 3 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 105 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 105 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 105 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 105 246 3 2 35 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 105 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 105 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 105 246 3 1 35 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 105 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 105 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 105
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 246 (allA_succ_of_accept 103 104 246 (accept_3_4 103 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 104 246 2 51 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 104 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 101 104 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 104 246 2 50 52 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 104 246
  (Polychromatic418967fa.accept_12_3_8_6_1_895 99 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 104 246 2 49 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 104 246 (accept_3_4 97 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 104 246 2 48 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 104 246 (Polychromatic418967fa.accept_10_5_4_6_1_319 95 104 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 104 246 2 47 52 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 104 246
  (Polychromatic418967fa.accept_7_2_6_1_1_73 93 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 104 246 2 46 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 104 246 (accept_3_4 91 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 104 246 2 45 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 104 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 89 104 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 104 246 2 44 52 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 104 246
  (Polychromatic418967fa.accept_9_6_5_3_1_205 87 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 104 246 2 43 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 104 246 (accept_3_4 85 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 104 246 2 42 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 104 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 83 104 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 104 246 2 41 52 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 104 246
  (Polychromatic418967fa.accept_12_9_8_6_1_466 81 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 104 246 2 40 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 104 246 (accept_3_4 79 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 104 246 2 39 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 104 246 (Polychromatic418967fa.accept_14_7_6_8_1_2856 77 104 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 246 2 38 52 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 246
  (Polychromatic418967fa.accept_7_5_6_1_1_407 75 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 104 246 2 37 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 104 246 (accept_3_4 73 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 104 246 2 36 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 104 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 71 104 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 246 2 35 52 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 246
  (Polychromatic418967fa.accept_9_6_5_3_1_205 69 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 104 246 2 34 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 104 246 (accept_3_4 67 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 104 246 2 33 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 104 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 104 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 104 246 2 32 52 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 104 246
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 104 246 2 31 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 104 246 (accept_3_4 61 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 104 246 2 30 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 104 246 (Polychromatic418967fa.accept_19_2_9_18_1_6651 59 104 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 246 2 29 52 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 246
  (Polychromatic418967fa.accept_12_9_8_6_1_466 57 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 246 2 28 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 104 246 (accept_3_4 55 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 246 2 27 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 53 104 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 246 2 26 52 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 246
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 246 2 25 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 246 (accept_3_4 49 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 246 2 24 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 104 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 104 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 246 2 23 52 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 246
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 104 246 2 22 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 104 246 (accept_3_4 43 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 246 2 21 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 246 (Polychromatic418967fa.accept_19_3_9_18_1_10979 41 104 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 246 2 20 52 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 246
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 246 2 19 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 246 (accept_3_4 37 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 246 2 18 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 104 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 104 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 246 2 17 52 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 246
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 104 246 2 16 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 104 246 (accept_3_4 31 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 104 246 2 15 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 104 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 104 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 246 2 14 52 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 246
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 104 246 2 13 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 104 246 (accept_3_4 25 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 246 2 12 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 104 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 104 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 246 2 11 52 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 246
  (Polychromatic418967fa.accept_11_10_5_4_1_711 21 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 246 2 10 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 104 246 (accept_3_4 19 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 104 246 2 9 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 104 246 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 104 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 246 2 8 52 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 246
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 104 246 2 7 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 104 246 (accept_3_4 13 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 104 246 2 6 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 104 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 104 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 104 246 2 5 52 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 104 246
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 104 246 2 4 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 104 246 (accept_3_4 7 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104
  246 2 3 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  104 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 104 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 104 246 2 2 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 104 246 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 104 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 246 2 1 52 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 246 (accept_3_4 1 104 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 246 (allA_succ_of_accept 102 103 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 102 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 246 (accept_3_5 101 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 103 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 100 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 246
  (Polychromatic418967fa.accept_10_9_3_6_1_686 99 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 246 (accept_3_5 98 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 96 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 246 (accept_3_5 95 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 94 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 246 (accept_3_5 92 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 91 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 90 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 246 (accept_3_5 89 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 88 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 246
  (Polychromatic418967fa.accept_7_3_5_1_1_72 87 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 246 (accept_3_5 86 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 246 (Polychromatic418967fa.accept_24_12_7_6_1_6244 84 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 246 (accept_3_5 83 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 82 103 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 246 (accept_3_5 80 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 79 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 78 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 246 (accept_3_5 77 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 76 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 246
  (Polychromatic418967fa.accept_17_7_1_8_1_6280 75 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 246 (accept_3_5 74 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 246 (Polychromatic418967fa.accept_17_4_1_8_1_5070 72 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 246 (accept_3_5 71 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 103 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 246 (accept_3_5 68 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 246 (accept_3_5 65 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 64 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 246
  (Polychromatic418967fa.accept_16_15_7_6_1_1453 63 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 103 246 (accept_3_5 62 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 103 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 103 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 246 (accept_3_5 59 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 246 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 246 (accept_3_5 56 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 246 (Polychromatic418967fa.accept_19_16_8_18_1_8139 54 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 246 (accept_3_5 53 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 103 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 246
  (Polychromatic418967fa.accept_9_6_4_3_1_203 51 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 246 (accept_3_5 50 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 246 (accept_3_5 47 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 246 (accept_3_5 44 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 246 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 246 (accept_3_5 41 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 246 (Polychromatic418967fa.accept_43_40_17_31_1_14791 40 103 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 246
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 246 (accept_3_5 38 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 246 (Polychromatic418967fa.accept_22_14_15_4_1_8623 36 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 246 (accept_3_5 35 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 103 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 246 (accept_3_5 32 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 246 (Polychromatic418967fa.accept_19_11_8_18_1_6631 30 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 246 (accept_3_5 29 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 103 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 246
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 246 (accept_3_5 26 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 246 (accept_3_5 23 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 246 (Polychromatic418967fa.accept_15_7_13_6_1_696 22 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 246 (accept_3_5 20 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 246 (accept_3_5 17 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 246
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 246 (accept_3_5 14 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 246 (Polychromatic418967fa.accept_21_12_19_15_1_8942 12 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 246 (accept_3_5 11 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 103 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 246 (accept_3_5 8 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 246 (accept_3_5 5 103 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 103 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 246
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 246 (accept_3_5 2 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 103 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  246))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 246 (allA_succ_of_accept 101 102 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 101 102 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 102 246 2 50 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 102 246 3 33 34 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 102 246 2 49 51 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 246
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 97 102 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 102 246 6 16 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 102 246 (Polychromatic418967fa.accept_11_7_3_4_1_729 95 102 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 102 246 2 47 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 102 246 3 31 34 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 102 246 2 46 51 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 246
  (Polychromatic418967fa.accept_10_1_2_6_1_638 91 102 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 102 246 6 15 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 102 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 89 102 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 102 246 2 44 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 102 246 3 29 34 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 102 246 2 43 51 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 102 246
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 85 102 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 102 246 6 14 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 102 246 (Polychromatic418967fa.accept_21_20_18_15_1_11881 83 102 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 102 246 2 41 51 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 102 246 3 27 34 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 102 246 2 40 51
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 102 246
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 79 102 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 102 246 6 13 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 102 246 (Polychromatic418967fa.accept_15_2_12_6_1_3063 77 102 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 246 2 38 51 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 102 246 3 25 34 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 102 246 2 37 51 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 102 246
  (Polychromatic418967fa.accept_7_3_4_1_1_71 73 102 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 246 6 12 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 246 (Polychromatic418967fa.accept_10_1_2_6_1_638 71 102 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 246 2 35 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 102 246 3 23 34 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 102 246 2 34 51 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 246
  (Polychromatic418967fa.accept_14_11_4_8_1_664 67 102 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 246 6 11 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 246 (Polychromatic418967fa.accept_15_5_12_6_1_639 65 102 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 246 2 32 51 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 102 246 3 21 34 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 102 246 2 31 51 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 61 102 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 246 6 10 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 102 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 246 2 29 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 102 246 3 19 34 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 102 246 2 28 51 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 246
  (Polychromatic418967fa.accept_15_10_12_6_1_3000 55 102 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 102 246 6 9 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 102 246 (Polychromatic418967fa.accept_13_1_11_12_1_1322 53 102 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 246 2 26 51 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 102 246 3 17 34 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 102 246 2 25 51
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 246
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 49 102 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 102 246 6 8 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 102 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 102 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 246 2 23 51 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 102 246 3 15 34 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 102 246 2 22 51 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 246
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 43 102 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 102 246 6 7 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 102 246 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 102 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 246 2 20 51 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 102 246 3 13 34 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 102 246 2 19 51 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 246
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 37 102 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 246 6 6 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 102 246 (Polychromatic418967fa.accept_15_5_12_6_1_639 35 102 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 246 2 17 51 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 102 246 3 11 34 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 102 246 2 16 51 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 246
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 102 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 246 6 5 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 102 246 (Polychromatic418967fa.accept_11_7_3_4_1_729 29 102 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 246 2 14 51 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 102 246 3 9 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 102 246 2 13 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 246
  (Polychromatic418967fa.accept_14_11_4_8_1_664 25 102 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 246 6 4 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 102 246 (Polychromatic418967fa.accept_13_10_11_12_1_1320 23 102 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 246 2 11 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 102 246 3 7 34 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 102 246 2 10 51 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 102 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 246 6 3 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 102 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 246 2 8 51 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 102 246 3 5 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 102 246 2 7 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 246
  (Polychromatic418967fa.accept_21_13_18_15_1_2837 13 102 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 102 246 6 2 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 102 246 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 102 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 246 2 5 51 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 102 246 3 3 34 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 102 246 2 4 51 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 246
  (Polychromatic418967fa.accept_11_7_3_4_1_729 7 102 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 102 246 6 1 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 102 246 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 102 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 246 2 2 51 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 102 246 3 1 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 102 246 2 1 51 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 246 (Polychromatic418967fa.accept_10_1_2_6_1_638 1
  102 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 246 (allA_succ_of_accept 100 101 246 (accept_3_4 100 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 101 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 98 101 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 246 (accept_3_4 97 101 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 246 (Polychromatic418967fa.accept_7_5_3_1_1_424
  96 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 101 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 101 246 (accept_3_4 94 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 101 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 93 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 101 246 (Polychromatic418967fa.accept_10_2_1_6_1_634 92 101 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 246 (accept_3_4 91 101 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 246 (Polychromatic418967fa.accept_21_6_17_15_1_2833 90 101
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 89 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 101 246 (accept_3_4 88 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 101 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 101 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 86 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 246 (accept_3_4 85 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 246 (Polychromatic418967fa.accept_13_6_10_12_1_2049 84 101 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 101 246 (accept_3_4 82 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 101 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 101 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 80 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 246 (accept_3_4 79 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 78 101 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 246
  (Polychromatic418967fa.accept_9_5_2_3_1_194 77 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 101 246 (accept_3_4 76 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 101 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 101 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 74 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 246 (accept_3_4 73 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 101 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 246 (accept_3_4 70 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 246 (accept_3_4 67 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 246 (Polychromatic418967fa.accept_19_9_6_18_1_730 66 101 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 246
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 246 (accept_3_4 64 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 62 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 246 (accept_3_4 61 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 101 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 246 (accept_3_4 58 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 246 (Polychromatic418967fa.accept_10_7_1_6_1_673 57 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 246 (Polychromatic418967fa.accept_20_16_1_6_1_6196 56 101 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 246 (accept_3_4 55 101 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 101 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 246
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 246 (accept_3_4 52 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 50 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 246 (accept_3_4 49 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 246 (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 101 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 101 246 (accept_3_4 46 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 101 246 (Polychromatic418967fa.accept_10_5_1_6_1_672 45 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 101 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 246 (accept_3_4 43 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 101 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 246
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 246 (accept_3_4 40 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 246 (Polychromatic418967fa.accept_24_14_5_6_1_11512 38 101 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 246 (accept_3_4 37 101 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 246 (Polychromatic418967fa.accept_16_4_5_6_1_8071 36 101
  246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 101 246 (accept_3_4 34 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 101 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 246 (accept_3_4 31 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 101 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 246
  (Polychromatic418967fa.accept_21_8_17_15_1_2834 29 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 101 246 (accept_3_4 28 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 101 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 101 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 101 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 246 (accept_3_4 25 101 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 246 (Polychromatic418967fa.accept_9_6_2_3_1_771
  24 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 246 (accept_3_4 22 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 246 (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 246 (Polychromatic418967fa.accept_11_9_2_4_1_707 20 101 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 246 (accept_3_4 19 101 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 101 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 246
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 246 (accept_3_4 16 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 246 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 246 (accept_3_4 13 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 101 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 101 246 (accept_3_4 10 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  101 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 101 246 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 246 (accept_3_4 7 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 101 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 246
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 246 (accept_3_4 4 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 101 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 246 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 246 (accept_3_4 1 101 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101
  246)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_246_segment_000))))))))))))))))))))))))))))))))))))))))))))


