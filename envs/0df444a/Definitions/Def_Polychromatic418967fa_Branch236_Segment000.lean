-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch236_Segment000
-- name    : Polychromatic418967fa_Branch236_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:37:33.681734+00:00
-- url     : https://prove2.me/theorems/b3f25f13-16be-4217-8a37-e6d5242737e2
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

def Polychromatic418967fa.branch_236_segment_000 : allB 125 236 :=
  allB_succ' 113 124 236 (Eq.refl Bool.true) (allA_of_3_0 113 124 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 114 123 236 (Eq.refl Bool.true) (allA_succ_of_accept 113 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 123 236 (accept_3_2 112 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 123 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 111 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 123 236 (Polychromatic418967fa.accept_32_14_27_12_1_14144 110 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 123 236 (accept_3_2 109 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 123 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 108 123
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 123 236 (accept_3_2 106 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 123 236 (Polychromatic418967fa.accept_13_1_6_2_1_377 105 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 123 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 104 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 123 236 (accept_3_2 103 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 123 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 102 123
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 123 236 (accept_3_2 100 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 123 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 99 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 123 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 98 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 236 (accept_3_2 97 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 123 236 (Polychromatic418967fa.accept_11_8_2_5_1_1769 96 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 123 236 (accept_3_2 94 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 123 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 93 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 123 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 92 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 236 (accept_3_2 91 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 123 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 90 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 123 236 (accept_3_2 88 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 123 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 123 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 86 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 236 (accept_3_2 85 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 123 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 123 236 (accept_3_2 82 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 123 236 (Polychromatic418967fa.accept_15_6_3_11_1_848 81 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 123 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 80 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 236 (accept_3_2 79 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 123 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 123 236 (accept_3_2 76 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 123 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 123 236 (Polychromatic418967fa.accept_11_8_2_5_1_1769 74 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 236 (accept_3_2 73 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 123 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 123 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 123 236 (accept_3_2 70 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 123 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 123 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 236 (accept_3_2 67 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 123 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 123 236 (accept_3_2 64 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 123 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 123 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 62 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 236 (accept_3_2 61 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 236 (Polychromatic418967fa.accept_13_8_6_2_1_865 60 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 123 236 (accept_3_2 58 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 123 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 123 236 (Polychromatic418967fa.accept_13_4_6_2_1_1437 56 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 236 (accept_3_2 55 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 123
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 123 236 (accept_3_2 52 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 123 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 123 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 236 (accept_3_2 49 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 123 236 (accept_3_2 46 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 123 236 (Polychromatic418967fa.accept_17_11_4_15_1_3150 45 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 123 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 236 (accept_3_2 43 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 123 236 (accept_3_2 40 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 123 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 123 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 38 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 236 (accept_3_2 37 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 123 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 236 (accept_3_2 34 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 236 (Polychromatic418967fa.accept_16_1_11_12_1_1774 33 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 236 (accept_3_2 31 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 236 (accept_3_2 28 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 236 (accept_3_2 25 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 236 (Polychromatic418967fa.accept_16_8_11_12_1_962 24 123 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 236 (accept_3_2 22 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 236 (accept_3_2 19 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 236 (accept_3_2 16 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 236 (accept_3_2 13 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 236 (accept_3_2 10 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 236 (accept_3_2 7 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 123 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 236 (accept_3_2 4 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 123 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 236 (accept_3_2 1 123 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 115 122 236 (Eq.refl Bool.true) (allA_succ_of_gcd 114 122 236 2 57 61 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 122 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 113 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 122 236 2 56 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 122 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 111 122 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 122 236 2 55 61 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 122 236 (accept_3_2 109 122 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 122 236 2 54 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 122 236 (Polychromatic418967fa.accept_7_2_3_5_1_34
  107 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 122 236 2 53 61 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 122 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 105 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 122 236 2 52 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 122 236 (accept_3_2 103 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 122 236 2 51 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 122 236 (Polychromatic418967fa.accept_10_1_2_6_1_638 101 122 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 122 236 2 50 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 122 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 99 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 122 236 2 49 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 122 236 (accept_3_2 97 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 122 236 2 48 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 122 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 95 122 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 122 236 2 47 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 122 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 93 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 122 236 2 46 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 122 236 (accept_3_2 91 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 122 236 2 45 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 122 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 89 122 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 122 236 2 44 61 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 122 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 87 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 122 236 2 43 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 122 236 (accept_3_2 85 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 122 236 2 42 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 122 236 (Polychromatic418967fa.accept_11_6_1_5_1_2388 83 122 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 122 236 2 41 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 122 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 81 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 122 236 2 40 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 122 236 (accept_3_2 79 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 122 236 2 39 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 122 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 122 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 122 236 2 38 61 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 122 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 75 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 122 236 2 37 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 122 236 (accept_3_2 73 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 122 236 2 36 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 122 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 122 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 122 236 2 35 61 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 122 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 69 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 122 236 2 34 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 122 236 (accept_3_2 67 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 122 236 2 33 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 122 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 122 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 122 236 2 32 61 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 236
  (Polychromatic418967fa.accept_17_12_3_15_1_5476 63 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 122 236 2 31 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 122 236 (accept_3_2 61 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 236 2 30 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 122 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 236 2 29 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 236 2 28 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 236 (accept_3_2 55 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 236 2 27 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 122 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 236 2 26 61 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 236 2 25 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 236 (accept_3_2 49 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 236 2 24 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 122 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 236 2 23 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 236
  (Polychromatic418967fa.accept_16_13_10_12_1_1811 45 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 122 236 2 22 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 122 236 (accept_3_2 43 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 236 2 21 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 236 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 122 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 236 2 20 61 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 236 2 19 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 236 (accept_3_2 37 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 236 2 18 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 122 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 236 2 17 61 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 236 2 16 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 236 (accept_3_2 31 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 236 2 15 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 122 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 236 2 14 61 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 236
  (Polychromatic418967fa.accept_16_11_10_12_1_4832 27 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 122 236 2 13 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 122 236 (accept_3_2 25 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 236 2 12 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 122 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 236 2 11 61 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 236 2 10 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 236 (accept_3_2 19 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 236 2 9 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 122 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 122 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 236 2 8 61 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 122 236 2 7 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 122 236 (accept_3_2 13 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 122 236 2 6 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 122 236 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 122 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 122 236 2 5 61 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 122 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 122 236 2 4 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 122 236 (accept_3_2 7 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122
  236 2 3 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  122 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 122 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 122 236 2 2 61 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 122 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 122 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 236 2 1 61 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 236 (accept_3_2 1 122 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 121 236 (Eq.refl Bool.true) (allA_of_3_0 116 121 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 117 120 236 (Eq.refl Bool.true) (allA_succ_of_gcd 116 120 236 4 29 30 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 120 236 (accept_3_2 115 120 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 120 236 2 57 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 120 236 (Polychromatic418967fa.accept_9_5_3_2_1_171
  113 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 120 236 4 28 30 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 120 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 111 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 120 236 2 55 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 120 236 (accept_3_2 109 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 120 236 4 27 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 120 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 107 120 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 120 236 2 53 60 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 120 236
  (Polychromatic418967fa.accept_9_6_3_2_1_431 105 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 120 236 4 26 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 120 236 (accept_3_2 103 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 120 236 2 51 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 120 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 101 120 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 120 236 4 25 30 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 120 236
  (Polychromatic418967fa.accept_16_3_8_12_1_2736 99 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 120 236 2 49 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 120 236 (accept_3_2 97 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 120 236 4 24 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 120 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 95 120 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 120 236 2 47 60 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 120 236
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 93 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 120 236 4 23 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 120 236 (accept_3_2 91 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 120 236 2 45 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 120 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 89 120 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 120 236 4 22 30 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 120 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 87 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 120 236 2 43 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 120 236 (accept_3_2 85 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 120 236 4 21 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 120 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 83 120 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 120 236 2 41 60 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 120 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 81 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 120 236 4 20 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 120 236 (accept_3_2 79 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 120 236 2 39 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 120 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 120 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 120 236 4 19 30 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 120 236
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 75 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 120 236 2 37 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 120 236 (accept_3_2 73 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 236 4 18 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 120 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 120 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 120 236 2 35 60 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 120 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 120 236 4 17 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 120 236 (accept_3_2 67 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 236 2 33 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 120 236 (Polychromatic418967fa.accept_16_1_8_12_1_405 65 120 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 120 236 4 16 30 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 120 236
  (Polychromatic418967fa.accept_13_11_3_2_1_863 63 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 120 236 2 31 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 120 236 (accept_3_2 61 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 236 4 15 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 120 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 236 2 29 60 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 120 236
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 57 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 120 236 4 14 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 120 236 (accept_3_2 55 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 236 2 27 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 120 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 120 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 236 4 13 30 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 120 236
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 120 236 2 25 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 120 236 (accept_3_2 49 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 236 4 12 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 236 (Polychromatic418967fa.accept_16_15_8_12_1_2737 47 120 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 236 2 23 60 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 120 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 120 236 4 11 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 120 236 (accept_3_2 43 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 236 2 21 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 120 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 236 4 10 30 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 120 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 120 236 2 19 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 120 236 (accept_3_2 37 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 236 4 9 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 120 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 120 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 236 2 17 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 33
  120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 120 236 4 8 30 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 236 (accept_3_2 31
  120 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 236 2 15 60 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 236
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 29 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 120 236 4 7 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 120 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 120 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 236 2 13 60 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 236 (accept_3_2 25 120 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 236 4 6 30 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 120 236 2 11 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 120 236 (Polychromatic418967fa.accept_16_5_8_12_1_1766 21 120 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 236 4 5 30 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 236 (accept_3_2 19 120 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 236 2 9 60 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 120 236 4 4 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 120 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 120 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 236 2 7 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 236 (accept_3_2 13 120 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 236 4 3 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 120 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 236 2 5 60 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 236
  (Polychromatic418967fa.accept_13_9_3_2_1_399 9 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 120 236 4 2 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 236 (accept_3_2 7 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120
  236 2 3 60 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  120 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 120 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 120 236 4 1 30 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 120 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 120 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 236 2 1 60 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 236 (accept_3_2 1 120 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 120
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 118 119 236 (Eq.refl Bool.true) (allA_succ_of_accept 117 119 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 117 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 119 236 (Polychromatic418967fa.accept_16_4_7_12_1_2734 116 119 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 119 236 (accept_3_2 115 119 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 119 236 (Polychromatic418967fa.accept_14_2_7_12_1_1485 114 119 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 119 236
  (Polychromatic418967fa.accept_10_3_9_6_1_94 113 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 119 236 (accept_3_2 112 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 119 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 110 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 119 236 (accept_3_2 109 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 119 236 (Polychromatic418967fa.accept_15_3_14_11_1_1579 108
  119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 119 236
  (Polychromatic418967fa.accept_8_3_7_4_1_42 107 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 119 236 (accept_3_2 106 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 119 236 (Polychromatic418967fa.accept_16_8_7_12_1_7207 104 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 119 236 (accept_3_2 103 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 119 236 (Polychromatic418967fa.accept_15_12_14_11_1_4375 102
  119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 119 236
  (Polychromatic418967fa.accept_16_5_7_12_1_7206 101 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 119 236 (accept_3_2 100 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 119 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 119 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 98 119
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 119 236 (accept_3_2 97 119
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 119 236
  (Polychromatic418967fa.accept_21_12_14_5_1_8204 96 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 119 236 (Polychromatic418967fa.accept_10_5_9_6_1_697 95 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 236 (accept_3_2 94 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 119 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 119 236
  (Polychromatic418967fa.accept_19_16_5_8_1_3253 92 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 119 236 (accept_3_2 91 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 119 236 (Polychromatic418967fa.accept_19_14_5_8_1_10077 90 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 119 236 (Polychromatic418967fa.accept_14_5_7_12_1_4006 89 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 236 (accept_3_2 88 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 119 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 236
  (Polychromatic418967fa.accept_12_2_11_8_1_504 86 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 119 236 (accept_3_2 85 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 119 236 (Polychromatic418967fa.accept_11_7_9_5_1_338 84 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 119 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 83 119 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 236 (accept_3_2 82 119 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 119 236
  (Polychromatic418967fa.accept_19_4_5_8_1_11520 80 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 119 236 (accept_3_2 79 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 119 236 (Polychromatic418967fa.accept_15_3_14_11_1_1579 78 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 119 236 (Polychromatic418967fa.accept_20_17_19_16_1_6996 77 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 119 236 (accept_3_2 76 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 119 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 236
  (Polychromatic418967fa.accept_12_2_11_8_1_504 74 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 119 236 (accept_3_2 73 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 119 236 (Polychromatic418967fa.accept_14_2_7_12_1_1485 72 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 119 236 (Polychromatic418967fa.accept_18_17_11_2_1_7782 71 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 119 236 (accept_3_2 70 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 119 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 236
  (Polychromatic418967fa.accept_16_4_7_12_1_2734 68 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 119 236 (accept_3_2 67 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 119 236 (Polychromatic418967fa.accept_16_2_7_12_1_3793 66 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 119 236 (Polychromatic418967fa.accept_10_5_9_6_1_697 65 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 236 (accept_3_2 64 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 119 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 236
  (Polychromatic418967fa.accept_11_7_9_5_1_338 62 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 119 236 (accept_3_2 61 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 119 236 (Polychromatic418967fa.accept_19_3_5_8_1_8790 60 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 119 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 59 119 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 236 (accept_3_2 58 119 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 236
  (Polychromatic418967fa.accept_16_8_7_12_1_7207 56 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 119 236 (accept_3_2 55 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 119 236 (Polychromatic418967fa.accept_19_16_5_8_1_3253 54 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 236 (Polychromatic418967fa.accept_10_3_9_6_1_94 53 119 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 236 (accept_3_2 52 119 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 236
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 236 (accept_3_2 49 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 236 (Polychromatic418967fa.accept_15_3_14_11_1_1579 48 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 236 (Polychromatic418967fa.accept_14_5_7_12_1_4006 47 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 236 (accept_3_2 46 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 119 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 236
  (Polychromatic418967fa.accept_14_2_7_12_1_1485 44 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 236 (accept_3_2 43 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 236 (Polychromatic418967fa.accept_15_12_14_11_1_4375 42 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 236 (Polychromatic418967fa.accept_19_3_5_8_1_8790 41 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 236 (accept_3_2 40 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 119 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 236
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 236 (accept_3_2 37 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 236 (Polychromatic418967fa.accept_16_4_7_12_1_2734 36 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 119 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 236 (accept_3_2 34 119 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 236
  (Polychromatic418967fa.accept_18_14_11_2_1_5068 32 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 119 236 (accept_3_2 31 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 119 236 (Polychromatic418967fa.accept_14_2_7_12_1_1485 30 119 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 236 (Polychromatic418967fa.accept_11_7_9_5_1_338 29 119
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 236 (accept_3_2 28 119
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 119 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 119 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 236 (accept_3_2 25 119 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 119 236 (Polychromatic418967fa.accept_16_8_7_12_1_7207 24 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 236
  (Polychromatic418967fa.accept_10_3_9_6_1_94 23 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 236 (accept_3_2 22 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 119 236 (Polychromatic418967fa.accept_16_4_7_12_1_2734 20 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 236 (accept_3_2 19 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 236 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 119
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 236
  (Polychromatic418967fa.accept_18_17_11_2_1_7782 17 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 119 236 (accept_3_2 16 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 119
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 236 (accept_3_2 13 119
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 236
  (Polychromatic418967fa.accept_15_12_14_11_1_4375 12 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 119 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 236 (accept_3_2 10 119 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 236
  (Polychromatic418967fa.accept_16_8_7_12_1_7207 8 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 236 (accept_3_2 7 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 236 (Polychromatic418967fa.accept_22_6_9_16_1_14143 6 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 236 (Polychromatic418967fa.accept_10_5_9_6_1_697 5 119 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 236 (accept_3_2 4 119 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 236
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 236 (accept_3_2 1 119 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 236 (allA_of_3_0 118 118 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 117 236
  (allA_succ_of_accept 116 117 236 (Polychromatic418967fa.accept_16_4_5_12_1_2749 116 117 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 236 (accept_3_2 115 117 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 117 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 114 117 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 117 236 (accept_3_2 112 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 117 236 (Polychromatic418967fa.accept_10_1_7_6_1_91 111 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 117 236 (Polychromatic418967fa.accept_19_15_3_8_1_8789 110 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 236 (accept_3_2 109 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 236 (Polychromatic418967fa.accept_11_9_7_5_1_749 108 117
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 236 (accept_3_2 106 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 117 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 105 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 117 236 (Polychromatic418967fa.accept_15_14_12_11_1_1572 104 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 236 (accept_3_2 103 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 102 117
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 117 236 (accept_3_2 100 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 117 236 (Polychromatic418967fa.accept_19_4_3_8_1_8788 99 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 117 236 (Polychromatic418967fa.accept_15_8_12_11_1_1570 98 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 236 (accept_3_2 97 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 236 (Polychromatic418967fa.accept_18_6_9_2_1_1575 96 117
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 117 236 (accept_3_2 94 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 117 236 (Polychromatic418967fa.accept_10_3_7_6_1_659 93 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 117 236 (Polychromatic418967fa.accept_21_8_12_5_1_8209 92 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 236 (accept_3_2 91 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 117 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 117
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 117 236 (accept_3_2 88 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 117 236 (Polychromatic418967fa.accept_14_3_5_12_1_4000 87 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 117 236 (Polychromatic418967fa.accept_11_9_7_5_1_749 86 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 236 (accept_3_2 85 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 236 (Polychromatic418967fa.accept_16_4_5_12_1_2749 84 117
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 117 236 (accept_3_2 82 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 117 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 81 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 117 236 (Polychromatic418967fa.accept_14_10_5_12_1_3995 80 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 236 (accept_3_2 79 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 117
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 236 (accept_3_2 76 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 117 236 (Polychromatic418967fa.accept_11_9_7_5_1_749 75 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 117 236 (Polychromatic418967fa.accept_15_14_12_11_1_1572 74 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 236 (accept_3_2 73 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 236 (Polychromatic418967fa.accept_16_8_5_12_1_3812 72 117
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 117 236 (accept_3_2 70 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 117 236 (Polychromatic418967fa.accept_21_6_12_5_1_6593 69 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 117 236 (Polychromatic418967fa.accept_15_8_12_11_1_1570 68 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 236 (accept_3_2 67 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 117
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 117 236 (accept_3_2 64 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 117 236 (Polychromatic418967fa.accept_10_3_7_6_1_659 63 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 117 236 (Polychromatic418967fa.accept_19_5_3_8_1_7302 62 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 236 (accept_3_2 61 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 236 (Polychromatic418967fa.accept_18_6_9_2_1_1575 60 117
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 236 (accept_3_2 58 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 117 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 117 236 (Polychromatic418967fa.accept_16_8_5_12_1_3812 56 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 236 (accept_3_2 55 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 117
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 117 236 (accept_3_2 52 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 117 236 (Polychromatic418967fa.accept_10_1_7_6_1_91 51 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 117 236 (Polychromatic418967fa.accept_21_8_12_5_1_8209 50 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 236 (accept_3_2 49 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 236 (Polychromatic418967fa.accept_21_6_12_5_1_6593 48 117
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 236 (accept_3_2 46 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 236 (Polychromatic418967fa.accept_14_3_5_12_1_4000 45 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 236 (Polychromatic418967fa.accept_15_14_12_11_1_1572 44 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 236 (accept_3_2 43 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 236 (Polychromatic418967fa.accept_11_9_7_5_1_749 42 117
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 236 (accept_3_2 40 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 117 236 (Polychromatic418967fa.accept_16_7_5_12_1_4824 39 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 117 236 (Polychromatic418967fa.accept_14_10_5_12_1_3995 38 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 236 (accept_3_2 37 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 236 (Polychromatic418967fa.accept_16_4_5_12_1_2749 36 117
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 236 (accept_3_2 34 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 117 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 236 (Polychromatic418967fa.accept_19_13_3_8_1_4534 32 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 236 (accept_3_2 31 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 117
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 236 (accept_3_2 28 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 117 236 (Polychromatic418967fa.accept_20_7_17_16_1_6976 27 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 117 236 (Polychromatic418967fa.accept_16_10_5_12_1_4925 26 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 236 (accept_3_2 25 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 236 (Polychromatic418967fa.accept_14_10_5_12_1_3995 24 117
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 236 (accept_3_2 22 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 117 236 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 236 (Polychromatic418967fa.accept_11_9_7_5_1_749 20 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 236 (accept_3_2 19 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 117
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 236 (accept_3_2 16 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 117 236 (Polychromatic418967fa.accept_19_15_3_8_1_8789 15 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 117 236 (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 236 (accept_3_2 13 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 236 (Polychromatic418967fa.accept_22_12_7_16_1_14142 12
  117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 236 (accept_3_2 10 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  117 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 117 236 (Polychromatic418967fa.accept_15_8_12_11_1_1570 8 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 236 (accept_3_2 7 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 117 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 236 (accept_3_2 4 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 236 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 117 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 236 (Polychromatic418967fa.accept_25_2_17_11_1_14141 2 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 236 (accept_3_2 1 117 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 236 (allA_succ_of_accept 115 116 236 (accept_3_2 115 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 116 236 2 57 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 116 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 113 116 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 116 236 4 28 29 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 116 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 111 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 116 236 2 55 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 116 236 (accept_3_2 109 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 116 236 4 27 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 116 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 107 116 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 116 236 2 53 58 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 116 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 105 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 116 236 4 26 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 116 236 (accept_3_2 103 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 116 236 2 51 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 116 236 (Polychromatic418967fa.accept_13_10_12_2_1_1460 101 116 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 116 236 4 25 29 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 116 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 99 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 116 236 2 49 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 116 236 (accept_3_2 97 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 116 236 4 24 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 116 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 95 116 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 116 236 2 47 58 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 116 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 93 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 116 236 4 23 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 116 236 (accept_3_2 91 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 116 236 2 45 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 116 236 (Polychromatic418967fa.accept_11_1_6_5_1_1732 89 116 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 116 236 4 22 29 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 116 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 87 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 116 236 2 43 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 116 236 (accept_3_2 85 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 116 236 4 21 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 116 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 83 116 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 116 236 2 41 58 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 116 236
  (Polychromatic418967fa.accept_13_3_12_2_1_385 81 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 116 236 4 20 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 116 236 (accept_3_2 79 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 116 236 2 39 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 116 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 116 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 116 236 4 19 29 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 116 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 75 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 116 236 2 37 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 116 236 (accept_3_2 73 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 116 236 4 18 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 116 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 71 116 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 116 236 2 35 58 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 116 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 116 236 4 17 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 116 236 (accept_3_2 67 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 116 236 2 33 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 116 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 116 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 116 236 4 16 29 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 116 236
  (Polychromatic418967fa.accept_16_15_4_12_1_2731 63 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 116 236 2 31 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 116 236 (accept_3_2 61 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 116 236 4 15 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 116 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 236 2 29 58 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 236 4 14 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 236 (accept_3_2 55 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 236 2 27 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 236 (Polychromatic418967fa.accept_13_1_12_2_1_384 53 116 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 236 4 13 29 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 236 2 25 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 236 (accept_3_2 49 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 236 4 12 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 236 (Polychromatic418967fa.accept_16_15_4_12_1_2731 47 116 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 236 2 23 58 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 236
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 236 4 11 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 236 (accept_3_2 43 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 236 2 21 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 116 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 236 4 10 29 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 236 2 19 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 236 (accept_3_2 37 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 236 4 9 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 116 236 (Polychromatic418967fa.accept_16_3_4_12_1_3799 35 116 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 236 2 17 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 33
  116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 116 236 4 8 29 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 116 236 (accept_3_2 31
  116 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 116 236 2 15 58 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 116 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 116 236 4 7 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 116 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 116 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 116 236 2 13 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 116 236 (accept_3_2 25 116 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 116 236 4 6 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 116 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 116 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 236 2 11 58 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 236 4 5 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 116 236 (accept_3_2 19 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  116 236 2 9 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 116 236 (Polychromatic418967fa.accept_13_4_12_2_1_1459 17 116 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 236 4 4 29 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 15
  116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 236 2 7 58 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 236 (accept_3_2 13
  116 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 236 4 3 29 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 236
  (Polychromatic418967fa.accept_16_11_4_12_1_1760 11 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 116 236 2 5 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 116 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 116 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 236 4 2 29 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 236 (accept_3_2 7 116 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116 236 2 3 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 116 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5
  116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 236 4 1 29 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 116 236 2 1 58 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 116 236 (accept_3_2 1 116 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 236 (allA_of_3_0 115 115 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 114 236
  (allA_succ_of_accept 113 114 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 113 114 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 114 236 2 56 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 114 236 (Polychromatic418967fa.accept_9_3_6_2_1_160
  111 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 114 236 2 55 57 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 114 236
  (accept_3_2 109 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 114 236 2 54 57 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 114 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 107 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 114 236 2 53 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 114 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 105 114 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 114 236 2 52 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 114 236 (accept_3_2 103 114 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 114 236 2 51 57 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 114 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 101 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 114 236 2 50 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 114 236 (Polychromatic418967fa.accept_12_3_6_8_1_969 99 114 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 114 236 2 49 57 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 114 236 (accept_3_2 97 114 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 114 236 2 48 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 114 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 95
  114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 114 236 2 47 57 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 114 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 93 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 114 236 2 46 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 114 236 (accept_3_2 91 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 236 2 45 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 89 114 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 114 236 2 44 57 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 114 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 87 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 114 236 2 43 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 114 236 (accept_3_2 85 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 236 2 42 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 236 (Polychromatic418967fa.accept_13_5_10_2_1_856 83 114 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 114 236 2 41 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 114 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 81 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 114 236 2 40 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 114 236 (accept_3_2 79 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 236 2 39 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 114 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 114 236 2 38 57 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 114 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 75 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 114 236 2 37 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 114 236 (accept_3_2 73 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 236 2 36 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 114 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 114 236 2 35 57 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 114 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 114 236 2 34 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 114 236 (accept_3_2 67 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 236 2 33 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 65 114 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 236 2 32 57 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 114 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 114 236 2 31 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 114 236 (accept_3_2 61 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 236 2 30 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 114 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 236 2 29 57 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 114 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 114 236 2 28 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 114 236 (accept_3_2 55 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 236 2 27 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 114 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 236 2 26 57 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 114 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 114 236 2 25 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 114 236 (accept_3_2 49 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 236 2 24 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 236 (Polychromatic418967fa.accept_13_8_10_2_1_1450 47 114 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 236 2 23 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 114 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 114 236 2 22 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 114 236 (accept_3_2 43 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 236 2 21 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 114 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 236 2 20 57 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 114 236 2 19 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 236 (accept_3_2 37 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 236 2 18 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 114 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 236 2 17 57 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 236 2 16 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 236 (accept_3_2 31 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 236 2 15 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 236 (Polychromatic418967fa.accept_13_3_10_2_1_381 29 114 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 236 2 14 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 114 236 2 13 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 114 236 (accept_3_2 25 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 236 2 12 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 114 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 236 2 11 57 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 236 2 10 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 114 236 (accept_3_2 19 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 236 2 9 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 114 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 114 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 236 2 8 57 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 236
  (Polychromatic418967fa.accept_10_5_4_6_1_319 15 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 114 236 2 7 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 114 236 (accept_3_2 13 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 236 2 6 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 114 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 114 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 236 2 5 57 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 236 2 4 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 236 (accept_3_2 7 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114
  236 2 3 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  114 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 114 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 236 2 2 57 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 114 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 114 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 236 2 1 57 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 236 (accept_3_2 1 114 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 236 (allA_succ_of_accept 112 113 236 (accept_3_2 112 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 113 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 110 113
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 236 (accept_3_2 109 113
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 108 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 107 113 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 236 (accept_3_2 106 113 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 104 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 113 236 (accept_3_2 103 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 113 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 102 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 113 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 101 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 236 (accept_3_2 100 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 113 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 98 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 236 (accept_3_2 97 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 96 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 95 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 236 (accept_3_2 94 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 236
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 92 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 113 236 (accept_3_2 91 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 113 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 90 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 113 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 89 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 236 (accept_3_2 88 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 86 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 236 (accept_3_2 85 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 113 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 83 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 236 (accept_3_2 82 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 80 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 236 (accept_3_2 79 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 77 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 236 (accept_3_2 76 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 74 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 236 (accept_3_2 73 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 236 (Polychromatic418967fa.accept_13_7_9_2_1_2167 72 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 236 (accept_3_2 70 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 236
  (Polychromatic418967fa.accept_10_8_3_6_1_685 68 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 236 (accept_3_2 67 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 236 (Polychromatic418967fa.accept_15_5_8_11_1_2350 65 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 236 (accept_3_2 64 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 113 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 62 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 236 (accept_3_2 61 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 236 (accept_3_2 58 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 236
  (Polychromatic418967fa.accept_16_8_1_12_1_984 56 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 236 (accept_3_2 55 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 236 (Polychromatic418967fa.accept_19_16_18_8_1_8784 54 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 236 (accept_3_2 52 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 236 (accept_3_2 49 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 236 (Polychromatic418967fa.accept_10_7_3_6_1_644 47 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 236 (accept_3_2 46 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 113 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 236 (accept_3_2 43 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 236 (accept_3_2 40 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 236 (accept_3_2 37 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 236 (Polychromatic418967fa.accept_16_4_1_12_1_1792 36 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 236 (accept_3_2 34 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 236 (accept_3_2 31 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 236 (accept_3_2 28 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 236 (accept_3_2 25 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 236 (Polychromatic418967fa.accept_19_4_18_8_1_10117 23 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 236 (accept_3_2 22 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 236 (accept_3_2 19 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 236 (accept_3_2 16 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 236 (accept_3_2 13 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 236 (accept_3_2 10 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 236 (accept_3_2 7 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 236 (accept_3_2 4 113 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 113 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 236 (accept_3_2 1 113 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 236 (allA_of_3_0 112 112 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 236
  (allA_succ_of_accept 110 111 236 (Polychromatic418967fa.accept_15_5_6_11_1_854 110 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 236 (accept_3_2 109 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 236 (Polychromatic418967fa.accept_15_3_6_11_1_855 108 111 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 236 (accept_3_2 106 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 105 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 104 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 236 (accept_3_2 103 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 102 111
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 236 (accept_3_2 100 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 99 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 98 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 236 (accept_3_2 97 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 96 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 236 (accept_3_2 94 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 236 (Polychromatic418967fa.accept_15_3_6_11_1_855 93 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 92 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 236 (accept_3_2 91 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 236 (accept_3_2 88 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 86 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 236 (accept_3_2 85 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 236 (Polychromatic418967fa.accept_15_9_6_11_1_1586 84 111 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 236 (accept_3_2 82 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 111 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 111 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 80 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 236 (accept_3_2 79 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 78 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 236 (accept_3_2 76 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 111 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 111 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 74 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 236 (accept_3_2 73 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 72 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 236 (accept_3_2 70 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 111 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 111 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 68 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 236 (accept_3_2 67 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 236 (accept_3_2 64 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 236 (Polychromatic418967fa.accept_15_3_6_11_1_855 63 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 236 (accept_3_2 61 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 236 (accept_3_2 58 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 236 (Polychromatic418967fa.accept_16_8_15_12_1_1747 56 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 236 (accept_3_2 55 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 111
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 236 (accept_3_2 52 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 50 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 236 (accept_3_2 49 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 236 (Polychromatic418967fa.accept_13_9_7_2_1_3869 48 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 236 (accept_3_2 46 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 236 (Polychromatic418967fa.accept_10_5_1_6_1_672 45 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 236 (accept_3_2 43 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 236 (accept_3_2 40 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 236 (Polychromatic418967fa.accept_20_18_11_16_1_6973 38 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 236 (accept_3_2 37 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 111 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 236 (accept_3_2 34 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 236 (accept_3_2 31 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 236 (accept_3_2 28 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 236 (accept_3_2 25 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 236 (accept_3_2 22 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 236 (Polychromatic418967fa.accept_13_8_7_2_1_2988 21 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 236 (Polychromatic418967fa.accept_14_6_13_12_1_810 20 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 236 (accept_3_2 19 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 111 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 236 (accept_3_2 16 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 236 (accept_3_2 13 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 236 (accept_3_2 10 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 236 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 236 (accept_3_2 7 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 111 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 236 (accept_3_2 4 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 111 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 236 (accept_3_2 1 111 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 236 (allA_succ_of_accept 109 110 236 (accept_3_2 109 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 110 236 2 54 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 110 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 107 110 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 110 236 2 53 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 110 236
  (Polychromatic418967fa.accept_13_1_6_2_1_377 105 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 110 236 2 52 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 110 236 (accept_3_2 103 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 110 236 2 51 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 110 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 101 110 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 110 236 2 50 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 110 236
  (Polychromatic418967fa.accept_13_8_6_2_1_865 99 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 110 236 2 49 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 110 236 (accept_3_2 97 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 110 236 2 48 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 110 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 95 110 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 110 236 2 47 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 110 236
  (Polychromatic418967fa.accept_19_17_15_8_1_5936 93 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 110 236 2 46 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 110 236 (accept_3_2 91 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 110 236 2 45 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 110 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 89 110 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 110 236 2 44 55 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 110 236
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 87 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 110 236 2 43 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 110 236 (accept_3_2 85 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 110 236 2 42 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 110 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 110 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 110 236 2 41 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 110 236
  (Polychromatic418967fa.accept_15_6_5_11_1_2378 81 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 110 236 2 40 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 110 236 (accept_3_2 79 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 110 236 2 39 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 110 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 110 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 110 236 2 38 55 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 110 236
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 75 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 110 236 2 37 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 110 236 (accept_3_2 73 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 110 236 2 36 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 110 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 110 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 110 236 2 35 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 110 236
  (Polychromatic418967fa.accept_13_4_6_2_1_1437 69 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 110 236 2 34 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 110 236 (accept_3_2 67 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 110 236 2 33 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 110 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 110 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 110 236 2 32 55 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 236
  (Polychromatic418967fa.accept_27_9_2_20_1_12263 63 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 110 236 2 31 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 110 236 (accept_3_2 61 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 236 2 30 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 110 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 236 2 29 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 236
  (Polychromatic418967fa.accept_17_6_8_15_1_10655 57 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 110 236 2 28 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 110 236 (accept_3_2 55 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 110 236 2 27 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 110 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 110 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 236 2 26 55 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 236
  (Polychromatic418967fa.accept_13_12_6_2_1_1441 51 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 236 2 25 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 236 (accept_3_2 49 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 236 2 24 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 110 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 236 2 23 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 236
  (Polychromatic418967fa.accept_19_7_15_8_1_1089 45 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 110 236 2 22 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 110 236 (accept_3_2 43 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 236 2 21 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 110 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 236 2 20 55 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 236
  (Polychromatic418967fa.accept_15_9_5_11_1_5416 39 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 236 2 19 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 236 (accept_3_2 37 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 236 2 18 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 110 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 236 2 17 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 236
  (Polychromatic418967fa.accept_25_8_10_11_1_14140 33 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 110 236 2 16 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 110 236 (accept_3_2 31 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 236 2 15 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 110 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 236 2 14 55 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 236
  (Polychromatic418967fa.accept_13_1_6_2_1_377 27 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 236 2 13 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 236 (accept_3_2 25 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 236 2 12 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 110 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 236 2 11 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 236
  (Polychromatic418967fa.accept_13_8_6_2_1_865 21 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 236 2 10 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 236 (accept_3_2 19 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 236 2 9 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 110 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 110 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 236 2 8 55 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 236
  (Polychromatic418967fa.accept_20_15_10_16_1_8506 15 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 110 236 2 7 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 110 236 (accept_3_2 13 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 110 236 2 6 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 110 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 110 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 236 2 5 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 236
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 236 2 4 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 236 (accept_3_2 7 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  236 2 3 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  110 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 110 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 110 236 2 2 55 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 110 236 (Polychromatic418967fa.accept_19_3_15_8_1_3232 3 110 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 236 2 1 55 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 236 (accept_3_2 1 110 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 236 (allA_of_3_0 109 109 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 236
  (allA_succ_of_accept 107 108 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 107 108 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 108 236 2 53 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 108 236
  (Polychromatic418967fa.accept_23_13_16_6_1_7665 105 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 108 236 4 26 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 108 236 (accept_3_2 103 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 108 236 2 51 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 108 236 (Polychromatic418967fa.accept_19_6_13_8_1_4508 101 108 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 108 236 4 25 27 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 108 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 99 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 108 236 2 49 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 108 236 (accept_3_2 97 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 236 4 24 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 108 236 (Polychromatic418967fa.accept_11_7_9_5_1_338 95 108 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 108 236 2 47 54 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 108 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 93 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 108 236 4 23 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 108 236 (accept_3_2 91 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 108 236 2 45 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 108 236 (Polychromatic418967fa.accept_13_11_4_2_1_2954 89 108 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 108 236 4 22 27 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 108 236
  (Polychromatic418967fa.accept_22_21_20_16_1_14139 87 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 108 236 2 43 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 108 236 (accept_3_2 85 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 236 4 21 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 236 (Polychromatic418967fa.accept_10_3_8_6_1_326 83 108 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 108 236 2 41 54 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 108 236
  (Polychromatic418967fa.accept_15_6_3_11_1_848 81 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 108 236 4 20 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 108 236 (accept_3_2 79 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 236 2 39 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 236 (Polychromatic418967fa.accept_13_12_4_2_1_2955 77 108 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 108 236 4 19 27 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 108 236
  (Polychromatic418967fa.accept_14_5_10_12_1_1454 75 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 108 236 2 37 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 108 236 (accept_3_2 73 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 236 4 18 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 108 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 236 2 35 54 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 108 236
  (Polychromatic418967fa.accept_21_6_3_5_1_8198 69 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 108 236 4 17 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 108 236 (accept_3_2 67 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 236 2 33 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 108 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 236 4 16 27 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 108 236
  (Polychromatic418967fa.accept_10_3_8_6_1_326 63 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 108 236 2 31 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 108 236 (accept_3_2 61 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 236 4 15 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 236 (Polychromatic418967fa.accept_15_14_3_11_1_850 59 108 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 236 2 29 54 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 108 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 108 236 4 14 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 108 236 (accept_3_2 55 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 236 2 27 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 236 (Polychromatic418967fa.accept_10_3_8_6_1_326 53 108 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 236 4 13 27 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 108 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 108 236 2 25 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 108 236 (accept_3_2 49 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 236 4 12 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 236 (Polychromatic418967fa.accept_14_5_10_12_1_1454 47 108 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 236 2 23 54 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 108 236
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 45 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 108 236 4 11 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 108 236 (accept_3_2 43 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 236 2 21 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 236 (Polychromatic418967fa.accept_19_3_13_8_1_4476 41 108 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 236 4 10 27 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 108 236
  (Polychromatic418967fa.accept_19_1_13_8_1_8779 39 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 108 236 2 19 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 108 236 (accept_3_2 37 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 236 4 9 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 236 (Polychromatic418967fa.accept_23_12_16_6_1_2656 35 108 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 236 2 17 54 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 236
  (Polychromatic418967fa.accept_10_3_8_6_1_326 33 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 108 236 4 8 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 108 236 (accept_3_2 31 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  108 236 2 15 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 108 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 108 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 236 4 7 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 108 236 (Polychromatic418967fa.accept_21_6_3_5_1_8198
  27 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 236 2 13 54 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 236
  (accept_3_2 25 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 236 4 6 27 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 108 236 2 11 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 108 236 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 108 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 108 236 4 5 27 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 236 (accept_3_2 19 108 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 236 2 9 54 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 236
  (Polychromatic418967fa.accept_23_17_16_6_1_7535 17 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 108 236 4 4 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 108 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 108 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 236 2 7 54 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 236 (accept_3_2 13 108 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 236 4 3 27 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 236
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 108 236 2 5 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 108 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 108 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 236 4 2 27 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 236 (accept_3_2 7 108 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 236 2 3 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 236 (Polychromatic418967fa.accept_13_5_4_2_1_846 5 108 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 236 4 1 27 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 108 236
  (Polychromatic418967fa.accept_10_3_8_6_1_326 3 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 108 236 2 1 54 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 236 (accept_3_2 1 108 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 236 (allA_succ_of_accept 106 107 236 (accept_3_2 106 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 107 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 104 107
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 236 (accept_3_2 103 107
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 102 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 101 107 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 236 (accept_3_2 100 107 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 236 (Polychromatic418967fa.accept_12_2_11_8_1_504
  98 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 107 236 (accept_3_2 97
  107 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 107 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 96 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 107 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 95 107 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 236 (accept_3_2 94 107 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 236 (Polychromatic418967fa.accept_13_1_3_2_1_1429
  92 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 107 236 (accept_3_2 91
  107 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 107 236
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 90 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 107 236 (Polychromatic418967fa.accept_13_11_3_2_1_863 89 107 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 236 (accept_3_2 88 107 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 236 (Polychromatic418967fa.accept_9_5_8_2_1_409
  86 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 107 236 (accept_3_2 85
  107 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 107 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 84 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 107 236 (Polychromatic418967fa.accept_10_3_7_6_1_659 83 107 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 236 (accept_3_2 82 107 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 236 (Polychromatic418967fa.accept_7_3_2_5_1_147
  80 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 107 236 (accept_3_2 79
  107 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 107 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 78 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 107 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 107 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 236 (accept_3_2 76 107 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 236 (Polychromatic418967fa.accept_7_4_2_5_1_527
  74 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 107 236 (accept_3_2 73
  107 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 107 236
  (Polychromatic418967fa.accept_16_8_11_12_1_962 72 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 107 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 71 107 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 236 (accept_3_2 70 107 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 236 (Polychromatic418967fa.accept_9_5_8_2_1_409
  68 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 107 236 (accept_3_2 67
  107 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 107 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 66 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 107 236 (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 107 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 236 (accept_3_2 64 107 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 236 (Polychromatic418967fa.accept_12_2_11_8_1_504
  62 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 236 (accept_3_2 61
  107 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 107 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 60 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 107 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 107 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 236 (accept_3_2 58 107 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 236
  (Polychromatic418967fa.accept_16_8_11_12_1_962 56 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 236 (accept_3_2 55 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 236 (Polychromatic418967fa.accept_15_9_2_11_1_2391 54 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 236 (accept_3_2 52 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 107 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 236 (accept_3_2 49 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 236 (accept_3_2 46 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 107 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 236
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 44 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 236 (accept_3_2 43 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 236 (accept_3_2 40 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 236 (accept_3_2 37 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 236 (Polychromatic418967fa.accept_11_3_8_5_1_336 36 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 236 (Polychromatic418967fa.accept_11_2_8_5_1_1219 35 107 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 236 (accept_3_2 34 107 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 107 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 236 (accept_3_2 31 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 236 (Polychromatic418967fa.accept_18_11_17_2_1_6349 29 107 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 236 (accept_3_2 28 107 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 236
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 236 (accept_3_2 25 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 236 (accept_3_2 22 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 107 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 236
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 20 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 236 (accept_3_2 19 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 236 (accept_3_2 16 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 236 (accept_3_2 13 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 236 (accept_3_2 10 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 107 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 236
  (Polychromatic418967fa.accept_16_8_11_12_1_962 8 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 236 (accept_3_2 7 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 236 (accept_3_2 4 107 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 236
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 2 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 236 (accept_3_2 1 107 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 236 (allA_of_3_0 106 106 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 236
  (allA_succ_of_accept 104 105 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 104 105 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 236 (accept_3_2 103 105 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 105 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 102 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 105 236 (accept_3_2 100 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 105 236 (Polychromatic418967fa.accept_10_9_5_6_1_691 99 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 105 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 98 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 236 (accept_3_2 97 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 236 (Polychromatic418967fa.accept_26_18_1_2_1_8639 96 105 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 236 (accept_3_2 94 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 105 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 93 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 105 236 (Polychromatic418967fa.accept_19_16_10_8_1_10067 92 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 236 (accept_3_2 91 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 105
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 236 (accept_3_2 88 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 236 (Polychromatic418967fa.accept_11_10_6_5_1_1239 87 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 86 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 236 (accept_3_2 85 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 236 (accept_3_2 82 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 105 236 (Polychromatic418967fa.accept_10_1_5_6_1_649 81 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 105 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 80 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 236 (accept_3_2 79 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 236 (Polychromatic418967fa.accept_11_1_6_5_1_1732 78 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 236 (accept_3_2 76 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 105 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 105 236 (Polychromatic418967fa.accept_10_4_5_6_1_651 74 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 236 (accept_3_2 73 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 236 (Polychromatic418967fa.accept_14_2_7_12_1_1485 72 105
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 236 (accept_3_2 70 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 105 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 69 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 105 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 236 (accept_3_2 67 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 105 236 (accept_3_2 64 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 105 236 (Polychromatic418967fa.accept_17_12_3_15_1_5476 63 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 105 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 62 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 236 (accept_3_2 61 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 236 (Polychromatic418967fa.accept_27_6_24_20_1_12284 60 105 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 236 (accept_3_2 58 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 105 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 105 236 (Polychromatic418967fa.accept_11_1_6_5_1_1732 56 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 236 (accept_3_2 55 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 236 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 105
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 236 (accept_3_2 52 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 105 236 (Polychromatic418967fa.accept_10_1_5_6_1_649 51 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 105 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 236 (accept_3_2 49 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 236 (accept_3_2 46 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 105 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 105 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 236 (accept_3_2 43 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 236 (accept_3_2 40 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 105 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 105 236 (Polychromatic418967fa.accept_13_12_1_2_1_845 38 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 236 (accept_3_2 37 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 236 (Polychromatic418967fa.accept_16_4_9_12_1_4829 36 105
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 236 (accept_3_2 34 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 105 236 (Polychromatic418967fa.accept_14_5_7_12_1_4006 33 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 105 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 236 (accept_3_2 31 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 236 (accept_3_2 28 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 105 236 (Polychromatic418967fa.accept_29_27_18_4_1_14138 27 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 236 (accept_3_2 25 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 236 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 105
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 236 (accept_3_2 22 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 105 236 (Polychromatic418967fa.accept_16_4_9_12_1_4829 20 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 236 (accept_3_2 19 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 105
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 236 (accept_3_2 16 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 236 (Polychromatic418967fa.accept_20_15_5_16_1_4026 15 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 105 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 236 (accept_3_2 13 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 236 (accept_3_2 10 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 236 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 236 (accept_3_2 7 105 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 236 (accept_3_2 4 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 105 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 236 (Polychromatic418967fa.accept_14_2_7_12_1_1485 2 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 236 (accept_3_2 1 105 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 105
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 236 (allA_succ_of_accept 103 104 236 (accept_3_2 103 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 104 236 2 51 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 104 236 (Polychromatic418967fa.accept_16_5_8_12_1_1766 101 104 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 104 236 4 25 26 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 104 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 99 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 104 236 2 49 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 104 236 (accept_3_2 97 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 104 236 4 24 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 104 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 95 104 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 104 236 2 47 52 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 104 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 93 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 104 236 4 23 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 104 236 (accept_3_2 91 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 104 236 2 45 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 104 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 89 104 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 104 236 4 22 26 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 104 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 87 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 104 236 2 43 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 104 236 (accept_3_2 85 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 104 236 4 21 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 104 236 (Polychromatic418967fa.accept_14_13_6_12_1_3126 83 104 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 104 236 2 41 52 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 104 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 81 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 104 236 4 20 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 104 236 (accept_3_2 79 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 104 236 2 39 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 104 236 (Polychromatic418967fa.accept_16_13_8_12_1_2723 77 104 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 236 4 19 26 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 75 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 104 236 2 37 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 104 236 (accept_3_2 73 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 104 236 4 18 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 104 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 71 104 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 236 2 35 52 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 69 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 104 236 4 17 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 104 236 (accept_3_2 67 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 104 236 2 33 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 104 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 65 104 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 104 236 4 16 26 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 104 236
  (Polychromatic418967fa.accept_15_3_14_11_1_1579 63 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 104 236 2 31 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 104 236 (accept_3_2 61 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 104 236 4 15 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 104 236 (Polychromatic418967fa.accept_16_11_8_12_1_1767 59 104 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 236 2 29 52 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 236 4 14 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 104 236 (accept_3_2 55 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 236 2 27 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 104 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 236 4 13 26 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 236 2 25 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 236 (accept_3_2 49 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 236 4 12 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 104 236 (Polychromatic418967fa.accept_16_15_8_12_1_2737 47 104 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 236 2 23 52 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 236
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 104 236 4 11 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 104 236 (accept_3_2 43 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 236 2 21 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 236 (Polychromatic418967fa.accept_14_13_6_12_1_3126 41 104 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 236 4 10 26 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 236 2 19 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 236 (accept_3_2 37 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 236 4 9 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 104 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 104 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 236 2 17 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 33
  104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 104 236 4 8 26 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 104 236 (accept_3_2 31
  104 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 104 236 2 15 52 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 104 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 104 236 4 7 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 104 236 (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 104 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 104 236 2 13 52 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 104 236 (accept_3_2 25 104 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 104 236 4 6 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 104 236 (Polychromatic418967fa.accept_16_7_8_12_1_4902
  23 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 236 2 11 52 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 236 4 5 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 104 236 (accept_3_2 19 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  104 236 2 9 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 104 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 236 4 4 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 15
  104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 236 2 7 52 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 236 (accept_3_2 13
  104 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 236 4 3 26 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 236 2 5 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 104 236 (Polychromatic418967fa.accept_16_9_8_12_1_979 9 104 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 236 4 2 26 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 236 (accept_3_2 7 104 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104 236 2 3 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 104 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 104 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 236 4 1 26 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 104 236 2 1 52 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 104 236 (accept_3_2 1 104 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 236 (allA_of_3_0 103 103 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 236 (allA_succ_of_accept 101
  102 236 (Polychromatic418967fa.accept_10_1_2_6_1_638 101 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 102 236 2 50 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 102 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 99 102 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 102 236 2 49 51 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 236 (accept_3_2 97 102 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 102 236 2 48 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 102 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 95 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 102 236 2 47 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 102 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 93 102 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 102 236 2 46 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 236 (accept_3_2 91 102 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 102 236 2 45 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 102 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 89
  102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 102 236 2 44 51 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 102 236
  (Polychromatic418967fa.accept_9_6_3_2_1_431 87 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 102 236 2 43 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 102 236 (accept_3_2 85 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 236 2 42 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 83 102 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 102 236 2 41 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 102 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 81 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 102 236 2 40 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 102 236 (accept_3_2 79 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 236 2 39 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 102 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 236 2 38 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 102 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 75 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 102 236 2 37 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 102 236 (accept_3_2 73 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 236 2 36 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 71 102 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 236 2 35 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 102 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 102 236 2 34 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 102 236 (accept_3_2 67 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 236 2 33 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 102 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 236 2 32 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 102 236
  (Polychromatic418967fa.accept_11_8_3_5_1_355 63 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 102 236 2 31 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 102 236 (accept_3_2 61 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 236 2 30 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 102 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 236 2 29 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 102 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 102 236 2 28 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 102 236 (accept_3_2 55 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 236 2 27 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 102 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 236 2 26 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 102 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 102 236 2 25 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 102 236 (accept_3_2 49 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 236 2 24 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 236 (Polychromatic418967fa.accept_19_9_7_8_1_3214 47 102 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 236 2 23 51 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 102 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 102 236 2 22 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 102 236 (accept_3_2 43 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 236 2 21 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 102 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 236 2 20 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 236 2 19 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 236 (accept_3_2 37 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 236 2 18 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 102 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 236 2 17 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 236
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 102 236 2 16 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 102 236 (accept_3_2 31 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 236 2 15 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 102 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 236 2 14 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 236 2 13 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 236 (accept_3_2 25 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 236 2 12 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 102 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 236 2 11 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 236 2 10 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 236 (accept_3_2 19 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 236 2 9 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 102 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 102 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 236 2 8 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 102 236 2 7 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 102 236 (accept_3_2 13 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 236 2 6 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 102 236 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 102 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 236 2 5 51 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 236 2 4 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 236 (accept_3_2 7 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102
  236 2 3 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  102 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 102 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 236 2 2 51 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 102 236 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 102 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 236 2 1 51 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 236 (accept_3_2 1 102 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 236 (allA_succ_of_accept 100 101 236 (accept_3_2 100 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 101 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 98 101
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 236 (accept_3_2 97 101
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 236
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 96 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 101 236 (Polychromatic418967fa.accept_10_5_1_6_1_672 95 101 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 101 236 (accept_3_2 94 101 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 101 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 101 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 101 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 92
  101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 236 (accept_3_2 91
  101 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 236
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 90 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 101 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 89 101 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 101 236 (accept_3_2 88 101 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 101 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 86 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 101 236 (accept_3_2 85 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 101 236 (Polychromatic418967fa.accept_13_6_10_2_1_1449 84 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 101 236 (Polychromatic418967fa.accept_13_5_10_2_1_856 83 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 101 236 (accept_3_2 82 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 101 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 101 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 236
  (Polychromatic418967fa.accept_22_14_13_16_1_14137 80 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 101 236 (accept_3_2 79 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 101 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 101 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 236 (Polychromatic418967fa.accept_10_7_1_6_1_673 77 101
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 236 (accept_3_2 76 101
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 75 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 101 236 (Polychromatic418967fa.accept_11_8_2_5_1_1769 74 101 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 236 (accept_3_2 73 101 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 101 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 101 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 71
  101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 236 (accept_3_2 70
  101 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 69 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 101 236 (Polychromatic418967fa.accept_13_3_10_2_1_381 68 101 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 236 (accept_3_2 67 101 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 101 236 (Polychromatic418967fa.accept_20_6_1_16_1_4059 66 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 65 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 236 (accept_3_2 64 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 62 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 236 (accept_3_2 61 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 236 (Polychromatic418967fa.accept_13_8_10_2_1_1450 60 101
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 236
  (Polychromatic418967fa.accept_19_2_6_8_1_3284 59 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 236 (accept_3_2 58 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 236 (Polychromatic418967fa.accept_16_8_5_12_1_3812 56 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 236 (accept_3_2 55 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 236 (Polychromatic418967fa.accept_19_16_6_8_1_8772 54 101
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 236
  (Polychromatic418967fa.accept_18_17_11_2_1_7782 53 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 101 236 (accept_3_2 52 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 101 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 101 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 101 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 236 (accept_3_2 49 101 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 236
  (Polychromatic418967fa.accept_17_14_16_15_1_5509 48 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 236 (Polychromatic418967fa.accept_10_7_1_6_1_673 47 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 236 (accept_3_2 46 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 101 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 236 (accept_3_2 43 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 101 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 236 (accept_3_2 40 101 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 236 (accept_3_2 37 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 236 (Polychromatic418967fa.accept_10_5_1_6_1_672 35 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 236 (accept_3_2 34 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 236
  (Polychromatic418967fa.accept_10_2_1_6_1_634 32 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 236 (accept_3_2 31 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 101 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 236 (accept_3_2 28 101 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 236 (accept_3_2 25 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 236 (Polychromatic418967fa.accept_13_11_10_2_1_3840 24 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 101 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 236 (accept_3_2 22 101 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 236
  (Polychromatic418967fa.accept_16_4_5_12_1_2749 20 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 236 (accept_3_2 19 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 236 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 101 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 236 (accept_3_2 16 101 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 236 (accept_3_2 13 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 236 (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 236 (accept_3_2 10 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 236 (accept_3_2 7 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 236 (Polychromatic418967fa.accept_13_6_10_2_1_1449 6 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 236 (Polychromatic418967fa.accept_10_5_1_6_1_672 5 101 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 236 (accept_3_2 4 101 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 101 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 236 (accept_3_2 1 101 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 236 (allA_of_3_0 100 100 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 236 (allA_succ_of_accept 98 99
  236 (Polychromatic418967fa.accept_13_7_8_2_1_1483 98 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 99 236 (accept_3_2 97 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 99 236 (Polychromatic418967fa.accept_15_6_9_11_1_858 96 99 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 99 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 236 (accept_3_2 94 99 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 236 (Polychromatic418967fa.accept_10_3_9_6_1_94 93
  99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 236
  (Polychromatic418967fa.accept_15_2_9_11_1_1551 92 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 236 (accept_3_2 91 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 90 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 236 (accept_3_2 88 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 99 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 236
  (Polychromatic418967fa.accept_19_10_4_8_1_11500 86 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 236 (accept_3_2 85 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 236 (Polychromatic418967fa.accept_13_6_8_2_1_1484 84 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 236 (accept_3_2 82 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 81 99 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 80 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 236 (accept_3_2 79 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 236 (accept_3_2 76 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 236 (Polychromatic418967fa.accept_10_5_9_6_1_697 75 99 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 74 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 236 (accept_3_2 73 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 236 (Polychromatic418967fa.accept_13_7_8_2_1_1483 72 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 236 (accept_3_2 70 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 99 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 236
  (Polychromatic418967fa.accept_16_4_3_12_1_4892 68 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 236 (accept_3_2 67 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 236 (accept_3_2 64 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 99 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 62 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 236 (accept_3_2 61 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 236 (accept_3_2 58 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 236 (Polychromatic418967fa.accept_16_9_3_12_1_1802 57 99 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 236
  (Polychromatic418967fa.accept_16_8_3_12_1_1819 56 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 236 (accept_3_2 55 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 236 (accept_3_2 52 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 236 (Polychromatic418967fa.accept_15_6_9_11_1_858 51 99 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 236
  (Polychromatic418967fa.accept_15_5_9_11_1_4398 50 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 236 (accept_3_2 49 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 236 (accept_3_2 46 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 99 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 236
  (Polychromatic418967fa.accept_27_17_18_20_1_6350 44 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 99 236 (accept_3_2 43 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 99 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 99 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 99 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 236 (accept_3_2 40 99 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 39
  99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 236 (accept_3_2 37 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 236 (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 236 (accept_3_2 34 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 236 (Polychromatic418967fa.accept_10_3_9_6_1_94 33 99 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 236 (accept_3_2 31 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 236 (accept_3_2 28 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 99 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 236
  (Polychromatic418967fa.accept_16_10_3_12_1_1758 26 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 236 (accept_3_2 25 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 236 (accept_3_2 22 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 236 (Polychromatic418967fa.accept_15_6_9_11_1_858 21 99 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 236 (accept_3_2 19 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 236 (accept_3_2 16 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 99 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 236
  (Polychromatic418967fa.accept_19_14_4_8_1_8807 14 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 236 (accept_3_2 13 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 236 (Polychromatic418967fa.accept_17_12_14_15_1_5561 12 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 236 (accept_3_2 10 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 236 (Polychromatic418967fa.accept_16_9_3_12_1_1802 9 99 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 236
  (Polychromatic418967fa.accept_16_8_3_12_1_1819 8 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 236 (accept_3_2 7 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  236 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 99 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 236 (accept_3_2 4 99 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 99 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 236 (Polychromatic418967fa.accept_15_2_9_11_1_1551
  2 99 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 236 (accept_3_2 1 99
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  236 (allA_succ_of_accept 97 98 236 (accept_3_2 97 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96
  98 236 2 48 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 98 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 95 98 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 98 236 2 47 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 98 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 93
  98 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 98 236 2 46 49 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 98 236 (accept_3_2 91
  98 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 98 236 2 45 49 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 98 236
  (Polychromatic418967fa.accept_12_5_2_8_1_172 89 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 98 236 2 44 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 98 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 87 98 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 98 236 2 43 49 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 98 236 (accept_3_2 85 98 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98 236 2 42 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 98 236 (Polychromatic418967fa.accept_10_3_8_6_1_326 83
  98 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 98 236 2 41 49 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 98 236
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 81 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 98 236 2 40 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 98 236 (accept_3_2 79 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 98 236 2 39 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 98 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 98 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 98 236 2 38 49 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 98 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 75 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 98 236 2 37 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 98 236 (accept_3_2 73 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 98 236 2 36 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 98 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 98 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 98 236 2 35 49 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 98 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 69 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 98 236 2 34 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 98 236 (accept_3_2 67 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 98 236 2 33 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 98 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 98 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 98 236 2 32 49 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 98 236
  (Polychromatic418967fa.accept_10_3_8_6_1_326 63 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 98 236 2 31 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 98 236 (accept_3_2 61 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 98 236 2 30 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 98 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 98 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 98 236 2 29 49 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 98 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 98 236 2 28 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 98 236 (accept_3_2 55 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 98 236 2 27 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 98 236 (Polychromatic418967fa.accept_10_3_8_6_1_326 53 98 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 98 236 2 26 49 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 98 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 98 236 2 25 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 98 236 (accept_3_2 49 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 98 236 2 24 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 98 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 98 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 236 2 23 49 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 236
  (Polychromatic418967fa.accept_17_11_13_15_1_2140 45 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 98 236 2 22 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 98 236 (accept_3_2 43 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 98 236 2 21 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 98 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 98 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 98 236 2 20 49 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 98 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 98 236 2 19 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 98 236 (accept_3_2 37 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 98 236 2 18 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 98 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 98 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 98 236 2 17 49 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 98 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 98 236 2 16 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 98 236 (accept_3_2 31 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 98 236 2 15 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 98 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 98 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 236 2 14 49 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 236
  (Polychromatic418967fa.accept_15_12_8_11_1_4383 27 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 236 2 13 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 98 236 (accept_3_2 25 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 98 236 2 12 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 98 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 98 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 98 236 2 11 49 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 98 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 98 236 2 10 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 98 236 (accept_3_2 19 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 98 236 2 9 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 98 236 (Polychromatic418967fa.accept_11_6_10_5_1_341 17 98 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 236 2 8 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  98 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 236 2 7 49 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 236 (accept_3_2 13
  98 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98 236 2 6 49 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 98 236
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 98 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 98 236 2 5 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 98 236 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 98 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 236 2 4 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 236 (accept_3_2 7 98 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 98 236 2 3 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 98 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 98 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 236 2 2 49 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 98
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 236 2 1 49 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 236 (accept_3_2 1 98
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  236 (allA_of_3_0 97 97 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 236 (allA_succ_of_accept 95 96 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 95 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 96 236 2 47 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 96 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 96 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 96 236 4 23 24 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 96 236 (accept_3_2 91 96 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 236 2 45 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 89
  96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 236 4 22 24 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 236
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 87 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 96 236 2 43 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 96 236 (accept_3_2 85 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 96 236 4 21 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 96 236 (Polychromatic418967fa.accept_19_7_1_8_1_7300 83 96 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 236 2 41 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 236 (Polychromatic418967fa.accept_13_3_5_2_1_1475
  81 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 96 236 4 20 24 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 236 (accept_3_2 79
  96 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 236 2 39 48 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 96 236 4 19 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 96 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 96 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 96 236 2 37 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 96 236 (accept_3_2 73 96 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 236 4 18 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 96 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 236 2 35 48 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 96 236
  (Polychromatic418967fa.accept_11_3_8_5_1_336 69 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 96 236 4 17 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 96 236 (accept_3_2 67 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96
  236 2 33 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  65 96 236 (Polychromatic418967fa.accept_15_5_6_11_1_854 65 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 96 236 4 16 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 96 236 (Polychromatic418967fa.accept_15_3_6_11_1_855 63 96 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 236 2 31 48 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 236 (accept_3_2 61 96 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 236 4 15 24 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 96 236 2 29 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 96 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 96 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 96 236 4 14 24 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96 236 (accept_3_2 55 96 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 236 2 27 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 53
  96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 236 4 13 24 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 96 236
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 51 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 96 236 2 25 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 96 236 (accept_3_2 49 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 236 4 12 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 96 236 (Polychromatic418967fa.accept_11_3_8_5_1_336 47 96 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 236 2 23 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 236 (Polychromatic418967fa.accept_18_9_6_2_1_2619
  45 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 96 236 4 11 24 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 236 (accept_3_2 43
  96 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 236 2 21 48 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 96 236 4 10 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 96 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 96 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 236 2 19 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 236 (accept_3_2 37 96 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 236 4 9 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 96 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 96 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 236 2 17 48 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 236
  (Polychromatic418967fa.accept_13_7_5_2_1_401 33 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 96 236 4 8 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 96 236 (accept_3_2 31 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96
  236 2 15 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 96 236 (Polychromatic418967fa.accept_13_3_5_2_1_1475 29 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 96 236 4 7 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 96 236 (Polychromatic418967fa.accept_18_9_6_2_1_2619 27 96 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 236 2 13 48 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 236 (accept_3_2 25 96 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 236 4 6 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 96 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 236 2 11 48 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 96 236 4 5 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 96 236 (accept_3_2 19 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96
  236 2 9 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  96 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 96 236 4 4 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 96 236 (Polychromatic418967fa.accept_19_15_1_8_1_4520 15 96 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 236 2 7 48 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 236 (accept_3_2 13 96 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 236 4 3 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 236 (Polychromatic418967fa.accept_19_11_1_8_1_10127 11 96
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 236 2 5 48 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 236
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 96 236 4 2 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 236 (accept_3_2 7 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 236
  2 3 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96
  236 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 96 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 96 236 4 1 24 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 96 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 96 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 236 2 1 48 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 236 (accept_3_2 1 96 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 236
  (allA_succ_of_accept 94 95 236 (accept_3_2 94 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 92 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 236 (accept_3_2 91 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 90 95 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 89 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 236 (accept_3_2 88 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 86 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 236 (accept_3_2 85 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 95 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 83 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 236 (accept_3_2 82 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 80 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 236 (accept_3_2 79 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 95 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 236
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 77 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 236 (accept_3_2 76 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 236 (Polychromatic418967fa.accept_10_4_5_6_1_651 74 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 236 (accept_3_2 73 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 95 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 71 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 236 (accept_3_2 70 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 236 (Polychromatic418967fa.accept_15_8_5_11_1_2358 68 95 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 236 (accept_3_2 67 95 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 95 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 65 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 236 (accept_3_2 64 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 62 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 236 (accept_3_2 61 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 95 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 236
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 236 (accept_3_2 58 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 236 (Polychromatic418967fa.accept_16_8_15_12_1_1747 56 95 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 236 (accept_3_2 55 95 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 236 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 95 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 236 (accept_3_2 52 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 236 (accept_3_2 49 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 95 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 236
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 47 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 236 (accept_3_2 46 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 236 (accept_3_2 43 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 95 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 236 (accept_3_2 40 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 236 (accept_3_2 37 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 95 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 236
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 236 (accept_3_2 34 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 236 (Polychromatic418967fa.accept_13_6_4_2_1_1433 32 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 236 (accept_3_2 31 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 95 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 236 (accept_3_2 28 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 236 (accept_3_2 25 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 95 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 236 (accept_3_2 22 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 236 (accept_3_2 19 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 236 (Polychromatic418967fa.accept_13_5_4_2_1_846 18 95 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 236 (accept_3_2 16 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 236 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 236 (accept_3_2 13 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 95 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 236
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 236 (accept_3_2 10 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 236 (accept_3_2 7 95 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 95 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 236
  (Polychromatic418967fa.accept_13_5_4_2_1_846 5 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 236 (accept_3_2 4 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 95 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 236 (accept_3_2 1 95 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 236
  (allA_of_3_0 94 94 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 236 (allA_succ_of_accept 92 93 236
  (Polychromatic418967fa.accept_19_16_17_8_1_8762 92 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 236 (accept_3_2 91 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 236 (accept_3_2 88 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 87 93 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 86 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 236 (accept_3_2 85 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 236 (Polychromatic418967fa.accept_16_4_13_12_1_1740 84 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 236 (accept_3_2 82 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 81 93 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 80 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 236 (accept_3_2 79 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 236 (accept_3_2 76 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 236 (Polychromatic418967fa.accept_21_12_9_5_1_6547 75 93 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 74 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 236 (accept_3_2 73 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 236 (Polychromatic418967fa.accept_16_8_13_12_1_3809 72 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 236 (accept_3_2 70 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 93 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 68 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 236 (accept_3_2 67 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 236 (accept_3_2 64 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 236 (Polychromatic418967fa.accept_14_7_9_12_1_3975 63 93 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 236 (accept_3_2 61 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 236 (accept_3_2 58 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 93 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 236
  (Polychromatic418967fa.accept_16_8_13_12_1_3809 56 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 236 (accept_3_2 55 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 236 (accept_3_2 52 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 93 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 236 (accept_3_2 49 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 236 (accept_3_2 46 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 93 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 236 (accept_3_2 43 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 236 (accept_3_2 40 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 93 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 236 (accept_3_2 37 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 236 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 236 (accept_3_2 34 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 93 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 236 (accept_3_2 31 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 236 (accept_3_2 28 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 236 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 93 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 236 (accept_3_2 25 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 236 (accept_3_2 22 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 236 (Polychromatic418967fa.accept_14_7_9_12_1_3975 21 93 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 236
  (Polychromatic418967fa.accept_16_4_13_12_1_1740 20 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 236 (accept_3_2 19 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 236 (accept_3_2 16 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 93 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 236 (accept_3_2 13 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 236 (Polychromatic418967fa.accept_18_12_3_2_1_756 12 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 236 (accept_3_2 10 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 93 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 236 (accept_3_2 7 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  236 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 236 (accept_3_2 4 93 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 93 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 236 (Polychromatic418967fa.accept_23_2_1_6_1_14136
  2 93 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 236 (accept_3_2 1 93
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 236
  (allA_succ_of_accept 91 92 236 (accept_3_2 91 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 92
  236 2 45 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  89 92 236 (Polychromatic418967fa.accept_26_11_14_2_1_14135 89 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 92 236 4 22 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 92 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 92 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 92 236 2 43 46 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 92 236 (accept_3_2 85 92 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 92 236 4 21 23 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 92 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 83 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 92 236 2 41 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 92 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 81 92 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 92 236 4 20 23 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 92 236 (accept_3_2 79 92 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 92 236 2 39 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 92 236 (Polychromatic418967fa.accept_13_12_1_2_1_845
  77 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 92 236 4 19 23 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 92 236
  (Polychromatic418967fa.accept_19_18_16_8_1_12903 75 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 92 236 2 37 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 92 236 (accept_3_2 73 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 92 236 4 18 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 92 236 (Polychromatic418967fa.accept_10_1_2_6_1_638 71 92 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 92 236 2 35 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 92 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 69
  92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 92 236 4 17 23 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 92 236 (accept_3_2 67
  92 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 92 236 2 33 46 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 92 236
  (Polychromatic418967fa.accept_11_10_4_5_1_359 65 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 92 236 4 16 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 92 236 (Polychromatic418967fa.accept_19_6_16_8_1_10116 63 92 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 92 236 2 31 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 92 236 (accept_3_2 61 92 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92 236 4 15 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 92 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 92 236 2 29 46 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 92 236
  (Polychromatic418967fa.accept_21_15_8_5_1_12668 57 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 92 236 4 14 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 92 236 (accept_3_2 55 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92
  236 2 27 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 92 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 92 236 4 13 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 92 236 (Polychromatic418967fa.accept_10_1_2_6_1_638 51 92 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 92 236 2 25 46 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 92 236 (accept_3_2 49 92 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92 236 4 12 23 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 92 236
  (Polychromatic418967fa.accept_19_9_16_8_1_2097 47 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 92 236 2 23 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 92 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 92 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 236 4 11 23 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 236 (accept_3_2 43 92 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 236 2 21 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 41
  92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 92 236 4 10 23 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 92 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 92 236 2 19 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 92 236 (accept_3_2 37 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 92 236 4 9 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 92 236 (Polychromatic418967fa.accept_13_9_1_2_1_2952 35 92 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 236 2 17 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 236 (Polychromatic418967fa.accept_21_12_8_5_1_5041
  33 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 92 236 4 8 23 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 92 236 (accept_3_2 31
  92 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92 236 2 15 46 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 92 236
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 29 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 92 236 4 7 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 92 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 92 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 236 2 13 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 236 (accept_3_2 25 92 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 236 4 6 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 92 236 (Polychromatic418967fa.accept_21_2_8_5_1_5057 23 92 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 236 2 11 46 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 236 4 5 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 92 236 (accept_3_2 19 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92
  236 2 9 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  92 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 92 236 4 4 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 92 236 (Polychromatic418967fa.accept_19_15_16_8_1_11553 15 92 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 236 2 7 46 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 236 (accept_3_2 13 92 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 236 4 3 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 92 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 11
  92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 236 2 5 46 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 236
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 92 236 4 2 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 92 236 (accept_3_2 7 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 236
  2 3 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92
  236 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 92 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 92 236 4 1 23 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 92 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 92 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 236 2 1 46 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 236 (accept_3_2 1 92 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 92
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 236
  (allA_of_3_0 91 91 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 236 (allA_succ_of_accept 89 90 236
  (Polychromatic418967fa.accept_19_13_14_8_1_4490 89 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 90 236 2 44 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 90 236 (Polychromatic418967fa.accept_12_3_6_8_1_969 87 90 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 90 236 2 43 45 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 90 236 (accept_3_2 85 90 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 236 2 42 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 236 (Polychromatic418967fa.accept_13_5_12_2_1_1423
  83 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 236 2 41 45 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 90 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 81 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 90 236 2 40 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 90 236 (accept_3_2 79 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 90 236 2 39 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 90 236 (Polychromatic418967fa.accept_16_13_10_12_1_1811 77 90 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 236 2 38 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 90 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 75 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 90 236 2 37 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 90 236 (accept_3_2 73 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 236 2 36 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 90 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 71 90 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 236 2 35 45 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 90 236 2 34 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 90 236 (accept_3_2 67 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 236 2 33 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 90 236 (Polychromatic418967fa.accept_20_5_10_16_1_9890 65 90 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 236 2 32 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 236
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 90 236 2 31 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 90 236 (accept_3_2 61 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 236 2 30 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 90 236 (Polychromatic418967fa.accept_16_11_10_12_1_4832 59 90 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 236 2 29 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 90 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 90 236 2 28 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 90 236 (accept_3_2 55 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 236 2 27 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 90 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 90 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 236 2 26 45 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 236 2 25 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 90 236 (accept_3_2 49 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 236 2 24 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 90 236 (Polychromatic418967fa.accept_17_13_5_15_1_8103 47 90 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 236 2 23 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 90 236 2 22 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 90 236 (accept_3_2 43 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 236 2 21 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 90 236 (Polychromatic418967fa.accept_11_8_2_5_1_1769 41 90 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 236 2 20 45 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 90 236 2 19 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 90 236 (accept_3_2 37 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 236 2 18 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 90 236 (Polychromatic418967fa.accept_16_3_10_12_1_4814 35 90 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 236 2 17 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 236 2 16 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 90 236 (accept_3_2 31 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 236 2 15 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 90 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 90 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 236 2 14 45 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 90 236 2 13 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 90 236 (accept_3_2 25 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 236 2 12 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 90 236 (Polychromatic418967fa.accept_13_10_12_2_1_1460 23 90 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 236 2 11 45 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 236 2 10 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 90 236 (accept_3_2 19 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 236 2 9 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 236 (Polychromatic418967fa.accept_13_4_12_2_1_1459 17 90 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 236 2 8 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 15
  90 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 236 2 7 45 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 236 (accept_3_2 13
  90 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 236 2 6 45 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 90 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 90 236 2 5 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 90 236 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 90 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 236 2 4 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 236 (accept_3_2 7 90 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 90 236 2 3 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 90 236 (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 90 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 236 2 2 45 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 236 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  90 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 236 2 1 45 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 236 (accept_3_2 1 90
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 236
  (allA_succ_of_accept 88 89 236 (accept_3_2 88 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 86 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 236 (accept_3_2 85 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 236
  (Polychromatic418967fa.accept_10_3_9_6_1_94 83 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 236 (accept_3_2 82 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 236 (Polychromatic418967fa.accept_14_10_5_12_1_3995 80 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 236 (accept_3_2 79 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 89 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 236
  (Polychromatic418967fa.accept_8_5_1_4_1_628 77 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 236 (accept_3_2 76 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 74 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 236 (accept_3_2 73 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 236 (Polychromatic418967fa.accept_11_6_1_5_1_2388 72 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 236
  (Polychromatic418967fa.accept_19_14_13_8_1_5943 71 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 236 (accept_3_2 70 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 236 (accept_3_2 67 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 236
  (Polychromatic418967fa.accept_10_5_9_6_1_697 65 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 236 (accept_3_2 64 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 236 (accept_3_2 61 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 236 (accept_3_2 58 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 236 (Polychromatic418967fa.accept_13_4_11_2_1_1458 56 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 236 (accept_3_2 55 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 236 (Polychromatic418967fa.accept_25_4_14_11_1_14134 54 89
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 236
  (Polychromatic418967fa.accept_8_5_1_4_1_628 53 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 236 (accept_3_2 52 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 236 (accept_3_2 49 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 236
  (Polychromatic418967fa.accept_18_11_17_2_1_6349 47 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 236 (accept_3_2 46 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 236 (Polychromatic418967fa.accept_17_10_4_15_1_2165 44 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 236 (accept_3_2 43 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 89 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 236 (accept_3_2 40 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 236 (accept_3_2 37 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 236 (Polychromatic418967fa.accept_13_10_11_2_1_3862 36 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 236
  (Polychromatic418967fa.accept_10_5_9_6_1_697 35 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 236 (accept_3_2 34 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 236 (accept_3_2 31 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 236
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 236 (accept_3_2 28 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 236 (accept_3_2 25 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 236 (accept_3_2 22 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 236 (Polychromatic418967fa.accept_16_4_9_12_1_4829 20 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 236 (accept_3_2 19 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 236 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 89
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 236
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 236 (accept_3_2 16 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 236 (accept_3_2 13 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 236
  (Polychromatic418967fa.accept_17_11_4_15_1_3150 11 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 236 (accept_3_2 10 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 236 (Polychromatic418967fa.accept_16_8_9_12_1_1737 8 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 236 (accept_3_2 7 89 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 89 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 236
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 236 (accept_3_2 4 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 89 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 89 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 236 (accept_3_2 1 89 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 236 (allA_of_3_0 88 88 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 236
  (allA_succ_of_accept 86 87 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 86 87 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 236 (accept_3_2 85 87 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 83
  87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 236 (accept_3_2 82 87
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 236
  (Polychromatic418967fa.accept_10_1_7_6_1_91 81 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 80 87 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 236 (accept_3_2 79 87 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 77
  87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 236 (accept_3_2 76 87
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 236 (Polychromatic418967fa.accept_8_3_7_4_1_42
  75 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 236
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 74 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 87 236 (accept_3_2 73 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 87 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 87 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 87 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 236 (accept_3_2 70 87 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 236 (Polychromatic418967fa.accept_16_5_7_12_1_7206
  69 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 68 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 236 (accept_3_2 67 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 236 (accept_3_2 64 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 236 (Polychromatic418967fa.accept_10_3_7_6_1_659 63 87 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 236 (accept_3_2 61 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 236 (Polychromatic418967fa.accept_19_3_11_8_1_3193 60 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 236 (accept_3_2 58 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 87 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 236
  (Polychromatic418967fa.accept_16_8_7_12_1_7207 56 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 236 (accept_3_2 55 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 236 (accept_3_2 52 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 87 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 236 (accept_3_2 49 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 236 (accept_3_2 46 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 236 (Polychromatic418967fa.accept_13_6_9_2_1_838 45 87 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 236 (accept_3_2 43 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 236 (accept_3_2 40 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 87 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 236
  (Polychromatic418967fa.accept_15_8_12_11_1_1570 38 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 236 (accept_3_2 37 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 236 (accept_3_2 34 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 236 (Polychromatic418967fa.accept_10_3_7_6_1_659 33 87 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 236 (accept_3_2 31 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 236 (accept_3_2 28 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 87 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 236 (accept_3_2 25 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 236 (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 236 (accept_3_2 22 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 87 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 236
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 20 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 236 (accept_3_2 19 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 236 (accept_3_2 16 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 87 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 236 (accept_3_2 13 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 236 (accept_3_2 10 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 87 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 236 (accept_3_2 7 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  236 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 87 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 236 (accept_3_2 4 87 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 87 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 236 (accept_3_2 1 87 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 236
  (allA_succ_of_accept 85 86 236 (accept_3_2 85 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 86
  236 2 42 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  83 86 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 86 236 2 41 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 86 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 81 86 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 86 236 2 40 43 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 86 236 (accept_3_2 79 86 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86 236 2 39 43 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 86 236
  (Polychromatic418967fa.accept_12_5_2_8_1_172 77 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 86 236 2 38 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 86 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 75 86 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 236 2 37 43 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 236 (accept_3_2 73 86 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 236 2 36 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 71
  86 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 86 236 2 35 43 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 86 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 69 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 86 236 2 34 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 86 236 (accept_3_2 67 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 86 236 2 33 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 86 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 86 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 86 236 2 32 43 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 86 236
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 63 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 86 236 2 31 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 86 236 (accept_3_2 61 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 86 236 2 30 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 86 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 86 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 86 236 2 29 43 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 86 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 86 236 2 28 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 86 236 (accept_3_2 55 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 86 236 2 27 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 86 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 86 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 236 2 26 43 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 236 2 25 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 86 236 (accept_3_2 49 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 86 236 2 24 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 86 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 86 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 86 236 2 23 43 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 86 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 86 236 2 22 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 86 236 (accept_3_2 43 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 86 236 2 21 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 86 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 86 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 236 2 20 43 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 86 236 2 19 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 86 236 (accept_3_2 37 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 86 236 2 18 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 86 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 86 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 236 2 17 43 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 236 2 16 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 86 236 (accept_3_2 31 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 86 236 2 15 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 86 236 (Polychromatic418967fa.accept_11_7_9_5_1_338 29 86 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 236 2 14 43 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 236
  (Polychromatic418967fa.accept_20_7_6_16_1_11369 27 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 236 2 13 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 86 236 (accept_3_2 25 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 86 236 2 12 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 86 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 86 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 86 236 2 11 43 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 86 236 2 10 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 86 236 (accept_3_2 19 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 86 236 2 9 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 86 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 86 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 236 2 8 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  86 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 236 2 7 43 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 236 (accept_3_2 13
  86 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86 236 2 6 43 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 86 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 86 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 86 236 2 5 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 86 236 (Polychromatic418967fa.accept_17_9_1_15_1_3156 9 86 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 236 2 4 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 236 (accept_3_2 7 86 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 86 236 2 3 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 86 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 86 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 236 2 2 43 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 86
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 236 2 1 43 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 236 (accept_3_2 1 86
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 236
  (allA_of_3_0 85 85 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 236 (allA_succ_of_accept 83 84 236
  (Polychromatic418967fa.accept_16_3_4_12_1_3799 83 84 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 84 236 2 41 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 84 236 (Polychromatic418967fa.accept_15_6_9_11_1_858 81 84 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 84 236 4 20 21 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 236 (accept_3_2 79 84 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 236 2 39 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 77
  84 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 236 4 19 21 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 236
  (Polychromatic418967fa.accept_10_5_4_6_1_319 75 84 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 236 2 37 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 84 236 (accept_3_2 73 84 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 84 236 4 18 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 84 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 84 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 236 2 35 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 69
  84 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 236 4 17 21 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 236 (accept_3_2 67
  84 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 236 2 33 42 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 236
  (Polychromatic418967fa.accept_10_5_4_6_1_319 65 84 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 236 4 16 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 84 236 (Polychromatic418967fa.accept_16_15_4_12_1_2731 63 84 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 236 2 31 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 236 (accept_3_2 61 84 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 236 4 15 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 84 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 236 2 29 42 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 236
  (Polychromatic418967fa.accept_16_9_4_12_1_4896 57 84 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 84 236 4 14 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 84 236 (accept_3_2 55 84 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84
  236 2 27 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 84 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 84 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 84 236 4 13 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 84 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 84 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 236 2 25 42 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 236 (accept_3_2 49 84 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 236 4 12 21 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 236
  (Polychromatic418967fa.accept_13_8_6_2_1_865 47 84 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 84 236 2 23 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 84 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 84 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 236 4 11 21 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 236 (accept_3_2 43 84 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 236 2 21 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 41
  84 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 236 4 10 21 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 236
  (Polychromatic418967fa.accept_16_7_4_12_1_1806 39 84 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 84 236 2 19 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 84 236 (accept_3_2 37 84 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 236 4 9 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 84 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 84 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 236 2 17 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 33
  84 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 236 4 8 21 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 236 (accept_3_2 31
  84 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 236 2 15 42 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 236
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 29 84 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 236 4 7 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 84 236 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 84 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 236 2 13 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 236 (accept_3_2 25 84 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 236 4 6 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 84 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 84 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 236 2 11 42 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 236
  (Polychromatic418967fa.accept_13_8_6_2_1_865 21 84 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 236 4 5 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 236 (accept_3_2 19 84 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84
  236 2 9 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  84 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 84 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 84 236 4 4 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 84 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 84 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 236 2 7 42 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 236 (accept_3_2 13 84 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 236 4 3 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 236 (Polychromatic418967fa.accept_16_11_4_12_1_1760 11 84
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 236 2 5 42 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 236
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 84 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 236 4 2 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 236 (accept_3_2 7 84 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 236
  2 3 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84
  236 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 84 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 236 4 1 21 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 84 236 (Polychromatic418967fa.accept_16_3_4_12_1_3799 3 84 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 236 2 1 42 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 236 (accept_3_2 1 84 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 83 236 (allA_succ_of_accept 82 83 236 (accept_3_2 82 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 83 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 83 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 83 236 (Polychromatic418967fa.accept_15_5_8_11_1_2350 80 83
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 236 (accept_3_2 79 83 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 78
  83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 236
  (Polychromatic418967fa.accept_10_7_3_6_1_644 77 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 236 (accept_3_2 76 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 74 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 236 (accept_3_2 73 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 236 (Polychromatic418967fa.accept_13_7_5_2_1_401 72 83 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 71 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 236 (accept_3_2 70 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 68 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 236 (accept_3_2 67 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 236 (Polychromatic418967fa.accept_19_9_7_8_1_3214 66 83 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 236
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 65 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 236 (accept_3_2 64 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 236 (accept_3_2 61 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 83 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 236
  (Polychromatic418967fa.accept_10_9_3_6_1_686 59 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 236 (accept_3_2 58 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 236 (Polychromatic418967fa.accept_11_1_6_5_1_1732 56 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 236 (accept_3_2 55 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 236 (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 83 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 53 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 236 (accept_3_2 52 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 50 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 236 (accept_3_2 49 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 83 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 236
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 236 (accept_3_2 46 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 236 (Polychromatic418967fa.accept_19_6_7_8_1_10108 44 83 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 236 (accept_3_2 43 83 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 236 (Polychromatic418967fa.accept_13_3_5_2_1_1475 42 83 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 236
  (Polychromatic418967fa.accept_16_9_3_12_1_1802 41 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 236 (accept_3_2 40 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 38 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 236 (accept_3_2 37 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 83 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 236
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 236 (accept_3_2 34 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 236 (accept_3_2 31 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 236 (Polychromatic418967fa.accept_13_4_5_2_1_1436 30 83 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 236 (accept_3_2 28 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 236 (accept_3_2 25 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 236 (Polychromatic418967fa.accept_16_8_3_12_1_1819 24 83 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 236
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 236 (accept_3_2 22 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 236 (Polychromatic418967fa.accept_13_7_5_2_1_401 20 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 236 (accept_3_2 19 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 83 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 236
  (Polychromatic418967fa.accept_10_7_3_6_1_644 17 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 236 (accept_3_2 16 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 236 (accept_3_2 13 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 236 (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 83 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 236 (accept_3_2 10 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 236 (accept_3_2 7 83 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 236 (Polychromatic418967fa.accept_14_6_13_12_1_810 6 83 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 236
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 236 (accept_3_2 4 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 83 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 236 (accept_3_2 1 83 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 236 (allA_of_3_0 82 82 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 236
  (allA_succ_of_accept 80 81 236 (Polychromatic418967fa.accept_15_5_6_11_1_854 80 81 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 236 (accept_3_2 79 81 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 77
  81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 236 (accept_3_2 76 81
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 236
  (Polychromatic418967fa.accept_10_5_1_6_1_672 75 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 236 (Polychromatic418967fa.accept_13_9_3_2_1_399 74 81 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 236 (accept_3_2 73 81 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 71
  81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 236 (accept_3_2 70 81
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 236 (Polychromatic418967fa.accept_16_4_1_12_1_1792 68 81 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 236 (accept_3_2 67 81 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 65
  81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 236 (accept_3_2 64 81
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 236
  (Polychromatic418967fa.accept_13_11_3_2_1_863 63 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 62 81 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 236 (accept_3_2 61 81 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 236 (Polychromatic418967fa.accept_18_6_9_2_1_1575 60 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 59
  81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 236 (accept_3_2 58 81
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 236 (Polychromatic418967fa.accept_7_1_4_5_1_35
  57 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 236
  (Polychromatic418967fa.accept_16_8_1_12_1_984 56 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 81 236 (accept_3_2 55 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  81 236 (Polychromatic418967fa.accept_11_10_4_5_1_359 54 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 81 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 236 (accept_3_2 52 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 81 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 50 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 236 (accept_3_2 49 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  81 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 81 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 236 (accept_3_2 46 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 81 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 44 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 236 (accept_3_2 43 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  81 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 81 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 236 (accept_3_2 40 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 236 (Polychromatic418967fa.accept_15_9_6_11_1_1586 39 81 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 236
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 38 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 236 (accept_3_2 37 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 236 (accept_3_2 34 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 236 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 81 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 236
  (Polychromatic418967fa.accept_10_2_1_6_1_634 32 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 236 (accept_3_2 31 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 236 (accept_3_2 28 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 81 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 236
  (Polychromatic418967fa.accept_20_6_1_16_1_4059 26 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 236 (accept_3_2 25 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 236 (Polychromatic418967fa.accept_13_11_3_2_1_863 24 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 236 (accept_3_2 22 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 81 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 236 (accept_3_2 19 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 236 (accept_3_2 16 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 81 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 236
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 14 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 236 (accept_3_2 13 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 236 (accept_3_2 10 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 81 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 236 (accept_3_2 7 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  236 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 236 (accept_3_2 4 81 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 236 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 81 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  81 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 236 (accept_3_2 1 81 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 236
  (allA_succ_of_accept 79 80 236 (accept_3_2 79 80 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 80
  236 2 39 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  77 80 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 80 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 80 236 4 19 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 80 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 75 80 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 80 236 2 37 40 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 80 236 (accept_3_2 73 80 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 80 236 4 18 20 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 80 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 71 80 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 80 236 2 35 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 80 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 69 80 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 236 4 17 20 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 236 (accept_3_2 67 80 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 236 2 33 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 80 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 65
  80 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 80 236 4 16 20 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 80 236
  (Polychromatic418967fa.accept_11_8_3_5_1_355 63 80 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 80 236 2 31 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 80 236 (accept_3_2 61 80 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 80 236 4 15 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 80 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 80 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 236 2 29 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 57
  80 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 80 236 4 14 20 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 80 236 (accept_3_2 55
  80 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80 236 2 27 40 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 80 236
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 53 80 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 80 236 4 13 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 80 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 80 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 236 2 25 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 236 (accept_3_2 49 80 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 236 4 12 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 236 (Polychromatic418967fa.accept_14_5_10_12_1_1454 47 80
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 236 2 23 40 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 80 236
  (Polychromatic418967fa.accept_24_21_8_20_1_14133 45 80 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 80 236 4 11 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 80 236 (accept_3_2 43 80 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 80 236 2 21 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 80 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 80 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 80 236 4 10 20 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 80 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 80 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 80 236 2 19 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 80 236 (accept_3_2 37 80 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 80 236 4 9 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 80 236 (Polychromatic418967fa.accept_17_1_12_15_1_1263 35 80 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 236 2 17 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 33
  80 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 80 236 4 8 20 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 80 236 (accept_3_2 31
  80 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 236 2 15 40 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 80 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 80 236 4 7 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 80 236 (Polychromatic418967fa.accept_22_5_14_16_1_14132 27 80 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 236 2 13 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 236 (accept_3_2 25 80 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 236 4 6 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 80 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 80 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 236 2 11 40 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 80 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 236 4 5 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 236 (accept_3_2 19 80 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  236 2 9 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 236 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 80 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 236 4 4 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 80 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 236 2 7 40 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 236 (accept_3_2 13 80 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 236 4 3 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 80 236 (Polychromatic418967fa.accept_21_11_17_5_1_8161 11 80
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 236 2 5 40 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 80 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 236 4 2 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 236 (accept_3_2 7 80 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 236
  2 3 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80
  236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 80 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 80 236 4 1 20 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 80 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 80 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 236 2 1 40 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 236 (accept_3_2 1 80 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 79 236 (allA_of_3_0 79 79 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 236
  (allA_succ_of_accept 77 78 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 78 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78 236 2 38 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 78 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 75
  78 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 78 236 2 37 39 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 236 (accept_3_2 73
  78 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 236 2 36 39 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 71 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 78 236 2 35 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 78 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 78 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 78 236 2 34 39 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 78 236 (accept_3_2 67 78 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 236 2 33 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 236 (Polychromatic418967fa.accept_20_5_18_16_1_1558
  65 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 236 2 32 39 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 236
  (Polychromatic418967fa.accept_10_3_8_6_1_326 63 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 78 236 2 31 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 78 236 (accept_3_2 61 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 236 2 30 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 78 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 78 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 236 2 29 39 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 78 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 78 236 2 28 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 78 236 (accept_3_2 55 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 236 2 27 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 78 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 78 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 236 2 26 39 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 78 236 2 25 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 78 236 (accept_3_2 49 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 236 2 24 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 78 236 (Polychromatic418967fa.accept_34_13_10_32_1_14131 47 78 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 236 2 23 39 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 78 236 2 22 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 78 236 (accept_3_2 43 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 236 2 21 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 78 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 78 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 236 2 20 39 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 78 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 78 236 2 19 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 78 236 (accept_3_2 37 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 236 2 18 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 78 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 78 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 236 2 17 39 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 236
  (Polychromatic418967fa.accept_10_3_8_6_1_326 33 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 236 2 16 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 78 236 (accept_3_2 31 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 236 2 15 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 78 236 (Polychromatic418967fa.accept_15_14_3_11_1_850 29 78 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 236 2 14 39 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 78 236 2 13 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 78 236 (accept_3_2 25 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 236 2 12 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 78 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 78 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 236 2 11 39 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 236 2 10 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 78 236 (accept_3_2 19 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 236 2 9 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 78 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 236 2 8 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 236 (Polychromatic418967fa.accept_12_3_6_8_1_969 15
  78 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 236 2 7 39 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 236 (accept_3_2 13
  78 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 236 2 6 39 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 78 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 78 236 2 5 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 78 236 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 78 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 236 2 4 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 236 (accept_3_2 7 78 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 78 236 2 3 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 78 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 78 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 236 2 2 39 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 78
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 236 2 1 39 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 236 (accept_3_2 1 78
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 236
  (allA_succ_of_accept 76 77 236 (accept_3_2 76 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 74 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 236 (accept_3_2 73 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 236 (Polychromatic418967fa.accept_14_2_7_12_1_1485 72 77 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 236 (accept_3_2 70 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 236 (Polychromatic418967fa.accept_13_3_12_2_1_385 68 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 236 (accept_3_2 67 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 77 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 236
  (Polychromatic418967fa.accept_8_1_5_4_1_388 65 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 236 (accept_3_2 64 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 236 (accept_3_2 61 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 77 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 236
  (Polychromatic418967fa.accept_19_2_1_8_1_7279 59 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 236 (accept_3_2 58 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 236 (Polychromatic418967fa.accept_13_4_12_2_1_1459 56 77 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 236 (accept_3_2 55 77 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 236 (Polychromatic418967fa.accept_15_9_2_11_1_2391 54 77
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 236 (accept_3_2 52 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 236 (accept_3_2 49 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 77 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 236
  (Polychromatic418967fa.accept_14_5_7_12_1_4006 47 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 236 (accept_3_2 46 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 236 (accept_3_2 43 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 77 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 236
  (Polychromatic418967fa.accept_8_1_5_4_1_388 41 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 236 (accept_3_2 40 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 236 (accept_3_2 37 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 236 (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 77 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 236 (accept_3_2 34 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 236 (Polychromatic418967fa.accept_13_6_12_2_1_4707 32 77 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 236 (accept_3_2 31 77 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 77 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 236
  (Polychromatic418967fa.accept_13_3_12_2_1_385 29 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 236 (accept_3_2 28 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 236 (accept_3_2 25 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 77 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 236
  (Polychromatic418967fa.accept_10_3_7_6_1_659 23 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 236 (accept_3_2 22 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 236 (Polychromatic418967fa.accept_15_5_2_11_1_1596 20 77 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 236 (accept_3_2 19 77 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 236 (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 77
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 236
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 236 (accept_3_2 16 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 236 (accept_3_2 13 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 77 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 236
  (Polychromatic418967fa.accept_10_1_7_6_1_91 11 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 236 (accept_3_2 10 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 236 (accept_3_2 7 77 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 77 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 236
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 236 (accept_3_2 4 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 77 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 77 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 236 (accept_3_2 1 77 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 236 (allA_of_3_0 76 76 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 236 (allA_succ_of_accept 74 75
  236 (Polychromatic418967fa.accept_10_4_5_6_1_651 74 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 236 (accept_3_2 73 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 236 (Polychromatic418967fa.accept_16_8_11_12_1_962 72 75 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 236 (accept_3_2 70 75 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 69
  75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 68 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 236 (accept_3_2 67 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 236 (accept_3_2 64 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 75 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 236 (accept_3_2 61 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 236 (accept_3_2 58 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 236 (Polychromatic418967fa.accept_13_5_10_2_1_856 57 75 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 236
  (Polychromatic418967fa.accept_16_8_11_12_1_962 56 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 236 (accept_3_2 55 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 236 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 236 (accept_3_2 52 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 75 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 236 (accept_3_2 49 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 236 (Polychromatic418967fa.accept_18_12_3_2_1_756 48 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 236 (accept_3_2 46 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 236 (Polychromatic418967fa.accept_13_6_10_2_1_1449 45 75 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 236 (accept_3_2 43 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 236 (accept_3_2 40 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 75 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 236
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 38 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 236 (accept_3_2 37 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 236 (Polychromatic418967fa.accept_16_4_11_12_1_1775 36 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 236 (accept_3_2 34 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 75 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 236 (accept_3_2 31 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 236 (accept_3_2 28 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 236 (Polychromatic418967fa.accept_18_9_3_2_1_3814 27 75 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 236 (accept_3_2 25 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 236 (accept_3_2 22 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 236 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 75 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 236
  (Polychromatic418967fa.accept_16_4_11_12_1_1775 20 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 236 (accept_3_2 19 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 236 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 236 (accept_3_2 16 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 75 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 236 (accept_3_2 13 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 236 (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 236 (accept_3_2 10 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 236 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 75 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 236 (accept_3_2 7 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  236 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 75 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 236 (accept_3_2 4 75 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 236 (Polychromatic418967fa.accept_13_3_10_2_1_381 3 75 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 236 (Polychromatic418967fa.accept_17_2_7_15_1_5525
  2 75 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 236 (accept_3_2 1 75
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 236 (allA_succ_of_accept
  73 74 236 (accept_3_2 73 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 236 2 36 37 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 71 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 236 2 35 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 74 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 74 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 236 2 34 37 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 236 (accept_3_2 67 74 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 236 2 33 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 65
  74 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 236 2 32 37 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 236
  (Polychromatic418967fa.accept_13_11_9_2_1_2969 63 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 74 236 2 31 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 74 236 (accept_3_2 61 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 74 236 2 30 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 74 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 74 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 74 236 2 29 37 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 74 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 74 236 2 28 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 74 236 (accept_3_2 55 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 74 236 2 27 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 74 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 74 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 74 236 2 26 37 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 74 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 74 236 2 25 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 74 236 (accept_3_2 49 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 74 236 2 24 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 74 236 (Polychromatic418967fa.accept_11_3_8_5_1_336 47 74 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 236 2 23 37 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 236
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 236 2 22 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 74 236 (accept_3_2 43 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 74 236 2 21 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 74 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 74 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 236 2 20 37 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 236
  (Polychromatic418967fa.accept_21_18_11_5_1_3487 39 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 236 2 19 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 74 236 (accept_3_2 37 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 74 236 2 18 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 74 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 74 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 236 2 17 37 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 236
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 33 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 74 236 2 16 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 74 236 (accept_3_2 31 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 74 236 2 15 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 74 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 74 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 236 2 14 37 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 236 2 13 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 74 236 (accept_3_2 25 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 74 236 2 12 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 74 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 74 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 236 2 11 37 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 236
  (Polychromatic418967fa.accept_16_5_10_12_1_4904 21 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 236 2 10 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 74 236 (accept_3_2 19 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 74 236 2 9 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 74 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 74 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 236 2 8 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 15
  74 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 236 2 7 37 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 236 (accept_3_2 13
  74 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 236 2 6 37 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74 236
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 74 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 74 236 2 5 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 74 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 74 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 236 2 4 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 236 (accept_3_2 7 74 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 74 236 2 3 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 74 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 74 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 236 2 2 37 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 236 (Polychromatic418967fa.accept_11_3_8_5_1_336 3
  74 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 236 2 1 37 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 236 (accept_3_2 1 74
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 236 (allA_of_3_0 73 73 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 236 (allA_succ_of_accept 71 72 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 71 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 72 236 2 35 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 72 236 (Polychromatic418967fa.accept_16_5_8_12_1_1766 69 72 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 236 4 17 18 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 236 (accept_3_2 67 72 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 236 2 33 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 236 (Polychromatic418967fa.accept_11_10_6_5_1_1239
  65 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 236 4 16 18 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 236
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 63 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 72 236 2 31 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 72 236 (accept_3_2 61 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 236 4 15 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 72 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 72 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 236 2 29 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 72 236 (Polychromatic418967fa.accept_13_5_7_2_1_852 57
  72 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 236 4 14 18 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 236 (accept_3_2 55
  72 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 236 2 27 36 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 72 236 4 13 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 72 236 (Polychromatic418967fa.accept_10_1_2_6_1_638 51 72 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 236 2 25 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 236 (accept_3_2 49 72 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 236 4 12 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 236 (Polychromatic418967fa.accept_13_8_7_2_1_2988 47 72 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 236 2 23 36 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 236 4 11 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 236 (accept_3_2 43 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72
  236 2 21 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 72 236 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 72 236 4 10 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 72 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 72 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 236 2 19 36 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 236 (accept_3_2 37 72 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 236 4 9 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 236 (Polychromatic418967fa.accept_13_9_7_2_1_3869
  35 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 236 2 17 36 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 236
  (Polychromatic418967fa.accept_16_1_8_12_1_405 33 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 236 4 8 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 236 (accept_3_2 31 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72
  236 2 15 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 72 236 (Polychromatic418967fa.accept_15_14_12_11_1_1572 29 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 72 236 4 7 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 72 236 (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 72 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 236 2 13 36 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 236 (accept_3_2 25 72 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 236 4 6 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 236 (Polychromatic418967fa.accept_11_1_6_5_1_1732
  23 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 236 2 11 36 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 236 4 5 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 236 (accept_3_2 19 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72
  236 2 9 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  72 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 236 4 4 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 236 (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 72 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 236 2 7 36 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 236 (accept_3_2 13 72 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 236 4 3 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 11
  72 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 236 2 5 36 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 236
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 236 4 2 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 236 (accept_3_2 7 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 236
  2 3 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72
  236 (Polychromatic418967fa.accept_13_5_7_2_1_852 5 72 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 72 236 4 1 18 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 72 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 72 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 236 2 1 36 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 236 (accept_3_2 1 72 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 236
  (allA_succ_of_accept 70 71 236 (accept_3_2 70 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 236 (accept_3_2 67 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 71 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 236
  (Polychromatic418967fa.accept_10_5_1_6_1_672 65 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 236 (accept_3_2 64 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 62 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 236 (accept_3_2 61 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 71 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 59 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 236 (accept_3_2 58 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 236 (Polychromatic418967fa.accept_13_4_6_2_1_1437 56 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 236 (accept_3_2 55 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 236 (Polychromatic418967fa.accept_21_12_8_5_1_5041 54 71 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 53 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 236 (accept_3_2 52 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 236 (accept_3_2 49 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 71 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 236
  (Polychromatic418967fa.accept_10_7_1_6_1_673 47 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 236 (accept_3_2 46 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 236 (Polychromatic418967fa.accept_18_8_17_2_1_1557 44 71 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 236 (accept_3_2 43 71 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 71 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 236 (accept_3_2 40 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 236 (accept_3_2 37 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 236 (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 71 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 236
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 236 (accept_3_2 34 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 236 (accept_3_2 31 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 71 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 236
  (Polychromatic418967fa.accept_17_12_3_15_1_5476 29 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 236 (accept_3_2 28 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 236 (accept_3_2 25 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 71 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 236 (accept_3_2 22 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 236 (accept_3_2 19 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 71 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 236 (accept_3_2 16 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 236 (accept_3_2 13 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 71 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 236 (accept_3_2 10 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 236 (Polychromatic418967fa.accept_13_8_6_2_1_865 8 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 236 (accept_3_2 7 71 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 71 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 236 (accept_3_2 4 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 71 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 236 (accept_3_2 1 71 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 236
  (allA_of_3_0 70 70 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 236 (allA_succ_of_accept 68 69 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 68 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 236 (accept_3_2 67 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 236 (accept_3_2 64 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 236 (Polychromatic418967fa.accept_10_3_9_6_1_94 63 69 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 236 (accept_3_2 61 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 236 (accept_3_2 58 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 69 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 236
  (Polychromatic418967fa.accept_16_8_5_12_1_3812 56 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 236 (accept_3_2 55 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 236 (accept_3_2 52 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 236 (Polychromatic418967fa.accept_13_12_4_2_1_2955 51 69 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 50 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 236 (accept_3_2 49 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 236 (accept_3_2 46 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 236 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 69 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 236 (accept_3_2 43 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 236 (accept_3_2 40 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 69 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 236
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 38 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 236 (accept_3_2 37 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 236 (accept_3_2 34 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 69 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 236 (accept_3_2 31 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 236 (accept_3_2 28 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 236 (Polychromatic418967fa.accept_20_7_9_16_1_11410 27 69 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 236 (accept_3_2 25 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 236 (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 236 (accept_3_2 22 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 69 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 236
  (Polychromatic418967fa.accept_14_6_13_12_1_810 20 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 236 (accept_3_2 19 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 236 (accept_3_2 16 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 69 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 236 (accept_3_2 13 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 236 (accept_3_2 10 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 69 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 236 (accept_3_2 7 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  236 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 236 (accept_3_2 4 69 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 69 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 236 (Polychromatic418967fa.accept_15_2_9_11_1_1551
  2 69 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 236 (accept_3_2 1 69
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 236 (allA_succ_of_accept 67 68
  236 (accept_3_2 67 68 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 236 2 33 34 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 236
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 65 68 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 236 4 16 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 68 236 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 68 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 236 2 31 34 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 236 (accept_3_2 61 68 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 236 4 15 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 236 (Polychromatic418967fa.accept_16_11_4_12_1_1760 59 68
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 236 2 29 34 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 68 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 236 4 14 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 68 236 (accept_3_2 55 68 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68
  236 2 27 34 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 68 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 68 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 68 236 4 13 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 68 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 68 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 236 2 25 34 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 236 (accept_3_2 49 68 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 236 4 12 17 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 236
  (Polychromatic418967fa.accept_16_15_4_12_1_2731 47 68 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 68 236 2 23 34 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 68 236 (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 68 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 236 4 11 17 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 236 (accept_3_2 43 68 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 236 2 21 34 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 236
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 41 68 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 68 236 4 10 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 68 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 68 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 236 2 19 34 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 236 (accept_3_2 37 68 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 236 4 9 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 68 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 68 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 236 2 17 34 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 68 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 236 4 8 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 68 236 (accept_3_2 31 68 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68
  236 2 15 34 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 68 236 (Polychromatic418967fa.accept_16_13_4_12_1_1805 29 68 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 68 236 4 7 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 68 236 (Polychromatic418967fa.accept_13_1_3_2_1_1429 27 68 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 236 2 13 34 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 236 (accept_3_2 25 68 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 236 4 6 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 236 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 68 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 236 2 11 34 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 68 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 236 4 5 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 236 (accept_3_2 19 68 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  236 2 9 34 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  68 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 68 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 68 236 4 4 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 68 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 68 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 236 2 7 34 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 236 (accept_3_2 13 68 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 236 4 3 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 68 236 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 68 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 236 2 5 34 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 236
  (Polychromatic418967fa.accept_13_9_3_2_1_399 9 68 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 236 4 2 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 236 (accept_3_2 7 68 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 236
  2 3 34 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  236 (Polychromatic418967fa.accept_13_5_3_2_1_1499 5 68 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 68 236 4 1 17 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 68 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 68 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 236 2 1 34 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 236 (accept_3_2 1 68 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 68 236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  67 236 (allA_of_3_0 67 67 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 236 (allA_succ_of_accept 65 66
  236 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 66 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 236 2 32 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 66 236 (Polychromatic418967fa.accept_12_3_6_8_1_969 63 66 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 236 2 31 33 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 236 (accept_3_2 61 66 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 236 2 30 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 59
  66 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 236 2 29 33 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 66 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 236 2 28 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 66 236 (accept_3_2 55 66 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 236 2 27 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 66 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 66 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 236 2 26 33 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 66 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 66 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 66 236 2 25 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 66 236 (accept_3_2 49 66 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 236 2 24 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 66 236 (Polychromatic418967fa.accept_14_5_10_12_1_1454 47 66 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 236 2 23 33 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 66 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 236 2 22 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 66 236 (accept_3_2 43 66 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 236 2 21 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 66 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 66 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 236 2 20 33 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 66 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 236 2 19 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 66 236 (accept_3_2 37 66 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 236 2 18 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 66 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 66 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 236 2 17 33 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 236
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 66 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 66 236 2 16 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 66 236 (accept_3_2 31 66 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 236 2 15 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 66 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 66 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 236 2 14 33 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 66 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 236 2 13 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 66 236 (accept_3_2 25 66 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 236 2 12 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 66 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 66 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 236 2 11 33 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 66 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 236 2 10 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 66 236 (accept_3_2 19 66 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 236 2 9 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 66 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 236 2 8 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  66 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 236 2 7 33 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 236 (accept_3_2 13
  66 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 236 2 6 33 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 236
  (Polychromatic418967fa.accept_19_11_9_8_1_11507 11 66 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 236 2 5 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 66 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 66 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 236 2 4 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 236 (accept_3_2 7 66 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 66 236 2 3 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 66 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 66 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 236 2 2 33 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 236 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  66 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 236 2 1 33 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 236 (accept_3_2 1 66
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 236 (allA_succ_of_accept 64 65 236
  (accept_3_2 64 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 65 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 236 (accept_3_2 61 65 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 65 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 59
  65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 236 (accept_3_2 58 65
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 236 (Polychromatic418967fa.accept_6_3_5_2_1_12
  57 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 236
  (Polychromatic418967fa.accept_16_8_1_12_1_984 56 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 65 236 (accept_3_2 55 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  65 236 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 65 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 65 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 236 (accept_3_2 52 65 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 65 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 65 236
  (Polychromatic418967fa.accept_11_6_10_5_1_341 50 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 65 236 (accept_3_2 49 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  65 236 (Polychromatic418967fa.accept_11_4_10_5_1_1202 48 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 65 236 (Polychromatic418967fa.accept_15_2_5_11_1_1563 47 65 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 236 (accept_3_2 46 65 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 65 236
  (Polychromatic418967fa.accept_10_4_5_6_1_651 44 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 65 236 (accept_3_2 43 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  65 236 (Polychromatic418967fa.accept_22_20_21_16_1_12616 42 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 65 236 (Polychromatic418967fa.accept_10_1_5_6_1_649 41 65 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 236 (accept_3_2 40 65 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 65 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 236 (accept_3_2 37 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 236 (Polychromatic418967fa.accept_15_6_5_11_1_2378 36 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 65 236 (Polychromatic418967fa.accept_14_7_9_12_1_3975 35 65 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 236 (accept_3_2 34 65 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 236 (accept_3_2 31 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 236 (Polychromatic418967fa.accept_20_10_5_16_1_7004 30 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 65 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 236 (accept_3_2 28 65 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 65 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 236
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 26 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 236 (accept_3_2 25 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  65 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 65 236 (Polychromatic418967fa.accept_15_8_5_11_1_2358 23 65 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 236 (accept_3_2 22 65 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 236
  (Polychromatic418967fa.accept_16_4_1_12_1_1792 20 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 236 (accept_3_2 19 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 65 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 236 (accept_3_2 16 65 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 65 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 236
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 236 (accept_3_2 13 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 236 (Polychromatic418967fa.accept_17_12_14_15_1_5561 12 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 65 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 236 (accept_3_2 10 65 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 236
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 236 (accept_3_2 7 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  236 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 65 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 65 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 236 (accept_3_2 4 65 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 65 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 236 (accept_3_2 1 65 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 236 (allA_of_3_0 64 64 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 236 (allA_succ_of_accept 62 63 236
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 62 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 236 (accept_3_2 61 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 236 (Polychromatic418967fa.accept_18_6_9_2_1_1575 60 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 236 (accept_3_2 58 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 236 (Polychromatic418967fa.accept_10_7_3_6_1_644 57 63 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 236
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 56 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 236 (accept_3_2 55 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 236 (accept_3_2 52 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 63 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 236
  (Polychromatic418967fa.accept_16_2_15_12_1_1744 50 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 236 (accept_3_2 49 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 236 (accept_3_2 46 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 236 (Polychromatic418967fa.accept_16_13_15_12_1_1748 45 63 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 236
  (Polychromatic418967fa.accept_14_2_7_12_1_1485 44 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 236 (accept_3_2 43 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 236 (accept_3_2 40 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 236 (Polychromatic418967fa.accept_10_9_3_6_1_686 39 63 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 236
  (Polychromatic418967fa.accept_10_8_3_6_1_685 38 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 236 (accept_3_2 37 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 236 (Polychromatic418967fa.accept_11_3_8_5_1_336 36 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 236 (accept_3_2 34 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 236 (Polychromatic418967fa.accept_14_5_7_12_1_4006 33 63 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 236
  (Polychromatic418967fa.accept_19_13_6_8_1_8741 32 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 236 (accept_3_2 31 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 236 (accept_3_2 28 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 63 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 236
  (Polychromatic418967fa.accept_19_7_6_8_1_12854 26 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 236 (accept_3_2 25 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 236 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 236 (accept_3_2 22 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 236 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 63 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 236
  (Polychromatic418967fa.accept_16_4_15_12_1_1745 20 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 236 (accept_3_2 19 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 236 (accept_3_2 16 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 236 (Polychromatic418967fa.accept_22_15_19_16_1_14130 15 63 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 236
  (Polychromatic418967fa.accept_11_3_8_5_1_336 14 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 236 (accept_3_2 13 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 236 (Polychromatic418967fa.accept_19_12_6_8_1_12868 12 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 236 (accept_3_2 10 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 236 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 63 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 236
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 236 (accept_3_2 7 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  236 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 63 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 236 (accept_3_2 4 63 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 63 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 236 (Polychromatic418967fa.accept_11_2_8_5_1_1219 2
  63 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 236 (accept_3_2 1 63 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 236 (allA_succ_of_accept 61 62 236
  (accept_3_2 61 62 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 236 2 30 31 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 62 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 236 2 29 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 62 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 62 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 236 2 28 31 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 236 (accept_3_2 55 62 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 236 2 27 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 53
  62 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 236 2 26 31 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 62 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 236 2 25 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 62 236 (accept_3_2 49 62 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 62 236 2 24 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 62 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 62 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 236 2 23 31 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 236
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 45 62 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 236 2 22 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 62 236 (accept_3_2 43 62 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 62 236 2 21 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 62 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 62 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 62 236 2 20 31 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 62 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 62 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 62 236 2 19 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 62 236 (accept_3_2 37 62 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 62 236 2 18 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 62 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 62 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 236 2 17 31 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 62 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 236 2 16 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 62 236 (accept_3_2 31 62 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 62 236 2 15 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 62 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 62 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 236 2 14 31 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 236
  (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 62 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 236 2 13 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 62 236 (accept_3_2 25 62 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 62 236 2 12 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 62 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 62 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 62 236 2 11 31 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 62 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 62 236 2 10 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 62 236 (accept_3_2 19 62 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 62 236 2 9 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 62 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 62 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 236 2 8 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 15
  62 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 236 2 7 31 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 236 (accept_3_2 13
  62 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 236 2 6 31 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 62 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 62 236 2 5 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 62 236 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 62 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 236 2 4 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 236 (accept_3_2 7 62 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 236 2 3 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 62 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 236 2 2 31 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 62
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 236 2 1 31 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 236 (accept_3_2 1 62
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 236 (allA_of_3_0 61 61 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 236 (allA_succ_of_accept 59 60 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 60 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 236 2 29 30 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 60 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 60 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 236 4 14 15 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 236 (accept_3_2 55 60 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 236 2 27 30 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 53
  60 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 236 4 13 15 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 60 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 236 2 25 30 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 60 236 (accept_3_2 49 60 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 236 4 12 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 236 (Polychromatic418967fa.accept_24_23_12_20_1_14129 47 60 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 236 2 23 30 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 60 236
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 45 60 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 60 236 4 11 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 60 236 (accept_3_2 43 60 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60
  236 2 21 30 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 60 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 60 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 60 236 4 10 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 60 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 60 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 236 2 19 30 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 236 (accept_3_2 37 60 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 236 4 9 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 35
  60 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 236 2 17 30 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 236
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 60 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 236 4 8 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 236 (accept_3_2 31 60 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  236 2 15 30 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 60 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 60 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 236 4 7 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 60 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 236 2 13 30 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 236 (accept_3_2 25 60 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 236 4 6 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 60 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 236 2 11 30 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 60 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 236 4 5 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 236 (accept_3_2 19 60 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60
  236 2 9 30 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  60 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 60 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 236 4 4 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 60 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 60 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 236 2 7 30 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 236 (accept_3_2 13 60 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 236 4 3 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 236 (Polychromatic418967fa.accept_19_11_3_8_1_11517 11 60
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 236 2 5 30 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 60 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 236 4 2 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 236 (accept_3_2 7 60 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 236
  2 3 30 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60
  236 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 60 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 60 236 4 1 15 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 60 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 60 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 236 2 1 30 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 236 (accept_3_2 1 60 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 236
  (allA_succ_of_accept 58 59 236 (accept_3_2 58 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 236 (Polychromatic418967fa.accept_16_8_11_12_1_962 56 59 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 236 (accept_3_2 55 59 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 236 (Polychromatic418967fa.accept_11_10_4_5_1_359 54 59 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 236 (accept_3_2 52 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 59 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 236 (accept_3_2 49 59 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 59 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 236
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 236 (accept_3_2 46 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 59 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 236 (accept_3_2 43 59 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 59 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 236
  (Polychromatic418967fa.accept_22_19_15_16_1_4583 41 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 59 236 (accept_3_2 40 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 59 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 59 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 236 (accept_3_2 37 59 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 36
  59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 236 (accept_3_2 34 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 236 (Polychromatic418967fa.accept_11_10_4_5_1_359 32 59 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 236 (accept_3_2 31 59 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 59 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 236 (accept_3_2 28 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 59 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 236 (accept_3_2 25 59 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 59 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 236 (accept_3_2 22 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 236 (Polychromatic418967fa.accept_16_4_11_12_1_1775 20 59 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 236 (accept_3_2 19 59 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 236 (Polychromatic418967fa.accept_13_5_7_2_1_852 18 59 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 236 (accept_3_2 16 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 59 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 236 (accept_3_2 13 59 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 59 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 236
  (Polychromatic418967fa.accept_19_11_2_8_1_8802 11 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 236 (accept_3_2 10 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 59 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 236 (accept_3_2 7 59 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 59 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 236
  (Polychromatic418967fa.accept_10_5_9_6_1_697 5 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 236 (accept_3_2 4 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 59 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 236 (accept_3_2 1 59 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 236 (allA_of_3_0
  58 58 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 236 (allA_succ_of_accept 56 57 236
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 56 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 236 (accept_3_2 55 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 236 (accept_3_2 52 57 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 57 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 236 (accept_3_2 49 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 57 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 236 (accept_3_2 46 57 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 57 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 236 (accept_3_2 43 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 236 (accept_3_2 40 57 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 57 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 236 (accept_3_2 37 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 236 (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 57 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 236 (accept_3_2 34 57 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 57 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 236 (accept_3_2 31 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 236 (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 236 (accept_3_2 28 57 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 57 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 236 (accept_3_2 25 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 57 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 236 (accept_3_2 22 57 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 57 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 236 (accept_3_2 19 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 236 (accept_3_2 16 57 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 57 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 236 (accept_3_2 13 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 236 (Polychromatic418967fa.accept_13_12_5_2_1_2173 12 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 57 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 236 (accept_3_2 10 57 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 236 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 57 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 236 (accept_3_2 7 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  236 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 236 (accept_3_2 4 57 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 57 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 236 (Polychromatic418967fa.accept_16_2_9_12_1_46 2
  57 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 236 (accept_3_2 1 57 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 236 (allA_succ_of_accept 55 56 236 (accept_3_2 55 56 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 236 2 27 28 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 56 236 (Polychromatic418967fa.accept_16_5_8_12_1_1766 53 56 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 236 4 13 14 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 236
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 51 56 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 56 236 2 25 28 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 56 236 (accept_3_2 49 56 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 56 236 4 12 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 56 236 (Polychromatic418967fa.accept_16_15_8_12_1_2737 47 56 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 56 236 2 23 28 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 56 236 (Polychromatic418967fa.accept_13_6_4_2_1_1433
  45 56 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 236 4 11 14 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 236 (accept_3_2 43
  56 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 236 2 21 28 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 236
  (Polychromatic418967fa.accept_16_9_8_12_1_979 41 56 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 56 236 4 10 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 56 236 (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 56 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 56 236 2 19 28 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 56 236 (accept_3_2 37 56 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56 236 4 9 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 56 236 (Polychromatic418967fa.accept_16_3_8_12_1_2736 35 56 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 236 2 17 28 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 236
  (Polychromatic418967fa.accept_16_1_8_12_1_405 33 56 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 236 4 8 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 56 236 (accept_3_2 31 56 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56
  236 2 15 28 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 56 236 (Polychromatic418967fa.accept_16_13_8_12_1_2723 29 56 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 56 236 4 7 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 56 236 (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 56 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 236 2 13 28 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 236 (accept_3_2 25 56 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 236 4 6 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 236 (Polychromatic418967fa.accept_16_7_8_12_1_4902
  23 56 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 236 2 11 28 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 236
  (Polychromatic418967fa.accept_16_5_8_12_1_1766 21 56 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 236 4 5 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 236 (accept_3_2 19 56 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  236 2 9 28 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 236 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 56 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 236 4 4 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 236 (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 56 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 236 2 7 28 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 236 (accept_3_2 13 56 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 236 4 3 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56 236 (Polychromatic418967fa.accept_13_11_4_2_1_2954
  11 56 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 236 2 5 28 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 236
  (Polychromatic418967fa.accept_16_9_8_12_1_979 9 56 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 236 4 2 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 56 236 (accept_3_2 7 56 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 236
  2 3 28 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56
  236 (Polychromatic418967fa.accept_13_5_4_2_1_846 5 56 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 56 236 4 1 14 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 56 236 (Polychromatic418967fa.accept_16_3_8_12_1_2736 3 56 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 236 2 1 28 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 236 (accept_3_2 1 56 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 236)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 236 (allA_of_3_0 55
  55 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 236 (allA_succ_of_accept 53 54 236
  (Polychromatic418967fa.accept_19_15_16_8_1_11553 53 54 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 54 236 2 26 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 54 236 (Polychromatic418967fa.accept_12_3_6_8_1_969 51 54 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 236 2 25 27 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 236 (accept_3_2 49 54 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 236 2 24 27 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 236
  (Polychromatic418967fa.accept_15_2_9_11_1_1551 47 54 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 54 236 2 23 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 54 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 54 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 236 2 22 27 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 236 (accept_3_2 43 54 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 236 2 21 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 236
  (Polychromatic418967fa.accept_31_10_23_19_1_14128 41 54 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 54 236 2 20 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 54 236 (Polychromatic418967fa.accept_11_6_10_5_1_341 39 54 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 236 2 19 27 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 236 (accept_3_2 37 54 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 236 2 18 27 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 236
  (Polychromatic418967fa.accept_10_5_4_6_1_319 35 54 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 236 2 17 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 54 236 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 54 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 236 2 16 27 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 236 (accept_3_2 31 54 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 236 2 15 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 236 (Polychromatic418967fa.accept_17_12_3_15_1_5476
  29 54 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 236 2 14 27 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 54 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 236 2 13 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 54 236 (accept_3_2 25 54 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 236 2 12 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 236 (Polychromatic418967fa.accept_25_23_4_11_1_14127 23 54 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 236 2 11 27 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 54 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 54 236 2 10 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 54 236 (accept_3_2 19 54 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 236 2 9 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 236 (Polychromatic418967fa.accept_11_6_10_5_1_341 17 54 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 236 2 8 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 15
  54 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 236 2 7 27 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 236 (accept_3_2 13
  54 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 236 2 6 27 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 236
  (Polychromatic418967fa.accept_19_11_16_8_1_2098 11 54 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 54 236 2 5 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 54 236 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 54 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 236 2 4 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 236 (accept_3_2 7 54 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 54 236 2 3 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 54 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 54 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 236 2 2 27 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 236 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  54 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 236 2 1 27 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 236 (accept_3_2 1 54
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 236))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 236 (allA_succ_of_accept 52 53 236 (accept_3_2 52 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 53 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 53 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 53 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 53 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 236 (accept_3_2 49 53 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 48
  53 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 236
  (Polychromatic418967fa.accept_10_7_3_6_1_644 47 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 236 (accept_3_2 46 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 53 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 236 (accept_3_2 43 53 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 53 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 236 (accept_3_2 40 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 38 53 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 236 (accept_3_2 37 53 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 53 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 236
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 35 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 236 (accept_3_2 34 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 53 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 236 (accept_3_2 31 53 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 53 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 236 (accept_3_2 28 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 53 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 236 (accept_3_2 25 53 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 53 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 236 (accept_3_2 22 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 53 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 236 (accept_3_2 19 53 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 53 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 236
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 236 (accept_3_2 16 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 53 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 236 (accept_3_2 13 53 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 53 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 236
  (Polychromatic418967fa.accept_18_11_17_2_1_6349 11 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 236 (accept_3_2 10 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 53 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 236 (accept_3_2 7 53 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 53 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 236 (accept_3_2 4 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 53 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 53 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 236 (accept_3_2 1 53 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 236))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 236 (allA_of_3_0 52 52
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 236 (allA_succ_of_accept 50 51 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 236 (accept_3_2 49 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 51 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 236 (accept_3_2 46 51 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 51 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 236 (accept_3_2 43 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 51 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 236 (accept_3_2 40 51 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 51 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 236 (accept_3_2 37 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 236 (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 236 (accept_3_2 34 51 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 236 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 51 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 236 (accept_3_2 31 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 51 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 236 (accept_3_2 28 51 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 236 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 51 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 236 (accept_3_2 25 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 236 (accept_3_2 22 51 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 51 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 236
  (Polychromatic418967fa.accept_11_9_7_5_1_749 20 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 236 (accept_3_2 19 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 51 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 236 (accept_3_2 16 51 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 51 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 236 (accept_3_2 13 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 236 (accept_3_2 10 51 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 236 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 51 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 236 (accept_3_2 7 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  236 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 51 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 51 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 236 (accept_3_2 4 51 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 51 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 2
  51 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 236 (accept_3_2 1 51 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 236)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 236 (allA_succ_of_accept 49 50 236 (accept_3_2 49 50 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 50 236 2 24 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 50 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 50 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 50 236 2 23 25 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 50 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 50 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 50 236 2 22 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 50 236 (accept_3_2 43 50 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 50 236 2 21 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 50 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 50 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 236 2 20 25 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 50 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 236 2 19 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 50 236 (accept_3_2 37 50 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 50 236 2 18 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 50 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 50 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 236 2 17 25 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 50 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 236 2 16 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 50 236 (accept_3_2 31 50 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 50 236 2 15 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 50 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 50 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 50 236 2 14 25 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 50 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 50 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 50 236 2 13 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 50 236 (accept_3_2 25 50 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 50 236 2 12 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 50 236 (Polychromatic418967fa.accept_11_1_6_5_1_1732 23 50 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 236 2 11 25 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 50 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 236 2 10 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 50 236 (accept_3_2 19 50 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 50 236 2 9 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 50 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 50 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 236 2 8 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  50 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 236 2 7 25 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 236 (accept_3_2 13
  50 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 236 2 6 25 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 50 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 236 2 5 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 236 (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 50 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 236 2 4 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 236 (accept_3_2 7 50 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 50 236 2 3 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 50 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 50 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 236 2 2 25 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 50
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 236 2 1 25 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 236 (accept_3_2 1 50
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 236))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 49 236 (allA_of_3_0 49 49 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 236
  (allA_succ_of_accept 47 48 236 (Polychromatic418967fa.accept_23_1_2_6_1_14126 47 48 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 236 2 23 24 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 236 (Polychromatic418967fa.accept_13_6_9_2_1_838 45
  48 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 236 4 11 12 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 236 (accept_3_2 43
  48 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 236 2 21 24 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 48 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 48 236 4 10 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 48 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 48 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 236 2 19 24 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 236 (accept_3_2 37 48 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 236 4 9 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 48 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 48 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 236 2 17 24 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 236
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 48 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 48 236 4 8 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 236 (accept_3_2 31 48 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48
  236 2 15 24 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 48 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 48 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 48 236 4 7 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 48 236 (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 48 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 236 2 13 24 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 236 (accept_3_2 25 48 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 236 4 6 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 48 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 236 2 11 24 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 236
  (Polychromatic418967fa.accept_11_10_4_5_1_359 21 48 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 236 4 5 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 236 (accept_3_2 19 48 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48
  236 2 9 24 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  48 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 48 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 236 4 4 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 48 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 236 2 7 24 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 236 (accept_3_2 13 48 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 236 4 3 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 48 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 236 2 5 24 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 236
  (Polychromatic418967fa.accept_22_9_4_16_1_4545 9 48 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 236 4 2 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 236 (accept_3_2 7 48 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 236
  2 3 24 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48
  236 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 48 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 48 236 4 1 12 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 48 236 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 48 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 236 2 1 24 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 236 (accept_3_2 1 48 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 236)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 236 (allA_succ_of_accept 46
  47 236 (accept_3_2 46 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 45 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 236 (Polychromatic418967fa.accept_28_16_19_12_1_14125 44 47 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 236 (accept_3_2 43 47 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 236 (Polychromatic418967fa.accept_17_8_13_15_1_2143 42 47 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 236
  (Polychromatic418967fa.accept_10_1_7_6_1_91 41 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 236 (accept_3_2 40 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 47 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 236 (accept_3_2 37 47 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 236 (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 47 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 236
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 236 (accept_3_2 34 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 236 (Polychromatic418967fa.accept_13_6_8_2_1_1484 32 47 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 236 (accept_3_2 31 47 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 236 (Polychromatic418967fa.accept_11_8_3_5_1_355 30 47 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 236
  (Polychromatic418967fa.accept_16_13_15_12_1_1748 29 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 47 236 (accept_3_2 28 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 47 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 47 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 236 (accept_3_2 25 47 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 236
  (Polychromatic418967fa.accept_14_10_5_12_1_3995 24 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 47 236 (Polychromatic418967fa.accept_10_3_7_6_1_659 23 47 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 236 (accept_3_2 22 47 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 47 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 47 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 236 (Polychromatic418967fa.accept_13_7_8_2_1_1483
  20 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 236 (accept_3_2 19
  47 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 236
  (Polychromatic418967fa.accept_16_2_15_12_1_1744 18 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 47 236 (Polychromatic418967fa.accept_14_3_5_12_1_4000 17 47 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 236 (accept_3_2 16 47 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 47 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 236 (Polychromatic418967fa.accept_12_2_11_8_1_504
  14 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 236 (accept_3_2 13
  47 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 236
  (Polychromatic418967fa.accept_24_12_23_20_1_14124 12 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 47 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 236 (accept_3_2 10 47 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 47 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 236
  (Polychromatic418967fa.accept_11_8_3_5_1_355 8 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 236 (accept_3_2 7 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  236 (Polychromatic418967fa.accept_13_6_8_2_1_1484 6 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 47 236 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 47 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 236 (accept_3_2 4 47 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 236
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 236 (accept_3_2 1 47 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  236))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 236 (allA_of_3_0 46 46 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 45 236 (allA_succ_of_accept 44 45 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 45
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 236 (accept_3_2 43 45 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 236 (Polychromatic418967fa.accept_12_6_9_8_1_165
  42 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 45 236 (accept_3_2 40 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  45 236 (Polychromatic418967fa.accept_10_9_5_6_1_691 39 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 45 236 (Polychromatic418967fa.accept_13_12_6_2_1_1441 38 45 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 236 (accept_3_2 37 45 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 45 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 236 (accept_3_2 34 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  45 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 45 236 (Polychromatic418967fa.accept_24_8_21_20_1_9094 32 45 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 236 (accept_3_2 31 45 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 45 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 45 236 (accept_3_2 28 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  45 236 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 45 236 (Polychromatic418967fa.accept_16_10_13_12_1_4873 26 45 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 236 (accept_3_2 25 45 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 236 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 45 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 236 (accept_3_2 22 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  45 236 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 45 236 (Polychromatic418967fa.accept_16_4_13_12_1_1740 20 45 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 236 (accept_3_2 19 45 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 45 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 236 (accept_3_2 16 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  45 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 45 236 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 45 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 236 (accept_3_2 13 45 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 236 (Polychromatic418967fa.accept_13_12_6_2_1_1441 12 45 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 45 236 (accept_3_2 10 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  45 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 45 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 45 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 236 (accept_3_2 7 45 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 236 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 45 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 45 236 (accept_3_2 4 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45
  236 (Polychromatic418967fa.accept_18_3_9_2_1_5053 3 45 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 45 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 45 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 236 (accept_3_2 1 45 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 45 236))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 236
  (allA_succ_of_accept 43 44 236 (accept_3_2 43 44 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44
  236 2 21 22 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 44 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 44 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 44 236 4 10 11 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 44 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 44 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 236 2 19 22 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 236 (accept_3_2 37 44 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 236 4 9 11 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 35
  44 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 236 2 17 22 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 44 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 236 4 8 11 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 236 (accept_3_2 31 44 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  236 2 15 22 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 44 236 (Polychromatic418967fa.accept_13_3_5_2_1_1475 29 44 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 236 4 7 11 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 44 236 (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 44 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 236 2 13 22 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 236 (accept_3_2 25 44 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 236 4 6 11 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 23
  44 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 236 2 11 22 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 44 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 44 236 4 5 11 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 44 236 (accept_3_2 19 44 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44
  236 2 9 22 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  44 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 44 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 44 236 4 4 11 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 44 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 44 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 236 2 7 22 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 236 (accept_3_2 13 44 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 236 4 3 11 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 44 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 44 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 236 2 5 22 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 236
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 44 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 44 236 4 2 11 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 44 236 (accept_3_2 7 44 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 236
  2 3 22 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44
  236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 44 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 44 236 4 1 11 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 44 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 44 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 236 2 1 22 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 236 (accept_3_2 1 44 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 236)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 236 (allA_of_3_0 43 43 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 236 (allA_succ_of_accept 41 42 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 42 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 236 2 20 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 42 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 42 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 236 2 19 21 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 236 (accept_3_2 37 42 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 236 2 18 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 35
  42 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 236 2 17 21 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 42 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 236 2 16 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 42 236 (accept_3_2 31 42 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 236 2 15 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 42 236 (Polychromatic418967fa.accept_11_7_9_5_1_338 29 42 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 236 2 14 21 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 42 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 42 236 2 13 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 42 236 (accept_3_2 25 42 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 236 2 12 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 42 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 42 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 236 2 11 21 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 42 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 236 2 10 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 42 236 (accept_3_2 19 42 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 236 2 9 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 42 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 236 2 8 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 236 (Polychromatic418967fa.accept_12_3_6_8_1_969 15
  42 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 236 2 7 21 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 236 (accept_3_2 13
  42 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 236 2 6 21 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 11 42 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 42 236 2 5 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 42 236 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 42 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 236 2 4 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 236 (accept_3_2 7 42 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 42 236 2 3 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 42 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 42 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 236 2 2 21 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 42
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 236 2 1 21 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 236 (accept_3_2 1 42
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 236)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41
  236 (allA_succ_of_accept 40 41 236 (accept_3_2 40 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 41 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 41 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 236 (accept_3_2 37 41 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 41 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 236 (accept_3_2 34 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 41 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 236 (accept_3_2 31 41 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 41 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 236 (accept_3_2 28 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 41 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 236 (accept_3_2 25 41 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 41 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 236
  (Polychromatic418967fa.accept_19_4_3_8_1_8788 23 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 236 (accept_3_2 22 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 236 (Polychromatic418967fa.accept_14_6_13_12_1_810 20 41 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 236 (accept_3_2 19 41 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 41 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 236 (accept_3_2 16 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 236 (Polychromatic418967fa.accept_11_3_8_5_1_336 14 41 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 236 (accept_3_2 13 41 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 41 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 236 (accept_3_2 10 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 41 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 236 (accept_3_2 7 41 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 41 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 236
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 236 (accept_3_2 4 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 41 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 41 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 236 (accept_3_2 1 41 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 236))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 236 (allA_of_3_0 40 40 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 236 (allA_succ_of_accept 38 39 236
  (Polychromatic418967fa.accept_25_13_14_11_1_14123 38 39 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 39 236 (accept_3_2 37 39 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 39 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 236 (accept_3_2 34 39 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 33
  39 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 39 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 236 (accept_3_2 31 39 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 39 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 39 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 236 (accept_3_2 28 39 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 39 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 39 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 236 (accept_3_2 25 39 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 39 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 236 (accept_3_2 22 39 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 236 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 39 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 39 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 236 (accept_3_2 19 39 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 39 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 39 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 236 (accept_3_2 16 39 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 39 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 39 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 236 (accept_3_2 13 39 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 236 (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 39 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 236 (accept_3_2 10 39 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 39 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 39 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 236 (accept_3_2 7 39 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  236 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 39 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 39 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 236 (accept_3_2 4 39 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 39 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  39 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 236 (accept_3_2 1 39 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 236))))))))))))))))))))))))))))))))))))))) (allB_succ 38 236
  (allA_succ_of_accept 37 38 236 (accept_3_2 37 38 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  236 2 18 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  35 38 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 38 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 236 2 17 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 236 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 38 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 236 2 16 19 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 236 (accept_3_2 31 38 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 236 2 15 19 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 38 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 236 2 14 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 38 236 (Polychromatic418967fa.accept_13_1_12_2_1_384 27 38 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 236 2 13 19 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 236 (accept_3_2 25 38 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 236 2 12 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 23
  38 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 236 2 11 19 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 236
  (Polychromatic418967fa.accept_20_1_18_16_1_12711 21 38 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 38 236 2 10 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 38 236 (accept_3_2 19 38 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 38 236 2 9 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 38 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 38 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 236 2 8 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  38 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 236 2 7 19 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 236 (accept_3_2 13
  38 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 236 2 6 19 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 38 236
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 38 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 38 236 2 5 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 38 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 38 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 236 2 4 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 236 (accept_3_2 7 38 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 38 236 2 3 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 38 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 38 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 236 2 2 19 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 236 (Polychromatic418967fa.accept_10_3_8_6_1_326 3
  38 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 236 2 1 19 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 236 (accept_3_2 1 38
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 236)))))))))))))))))))))))))))))))))))))) (allB_succ 37 236
  (allA_of_3_0 37 37 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 236 (allA_succ_of_accept 35 36 236
  (Polychromatic418967fa.accept_15_5_6_11_1_854 35 36 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 236 2 17 18 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 36 236 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 36 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 236 4 8 9 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 236 (accept_3_2 31 36 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 236 2 15 18 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 236 (Polychromatic418967fa.accept_13_3_10_2_1_381 29 36 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 236 4 7 9 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 36 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 236 2 13 18 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 36 236 (accept_3_2 25 36 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 236 4 6 9 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 236 (Polychromatic418967fa.accept_16_7_4_12_1_1806 23 36 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 236 2 11 18 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 236 (Polychromatic418967fa.accept_13_8_10_2_1_1450
  21 36 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 236 4 5 9 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 236 (accept_3_2 19
  36 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 236 2 9 18 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 36 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 36 236 4 4 9 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 36 236 (Polychromatic418967fa.accept_16_15_4_12_1_2731 15 36 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 236 2 7 18 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 236 (accept_3_2 13 36 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 236 4 3 9 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 36 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 36 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 236 2 5 18 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 36 236
  (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 36 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 36 236 4 2 9 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 236 (accept_3_2 7 36 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 236
  2 3 18 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36
  236 (Polychromatic418967fa.accept_13_5_10_2_1_856 5 36 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 36 236 4 1 9 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 36 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 36 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 236 2 1 18 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 236 (accept_3_2 1 36 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 36 236)))))))))))))))))))))))))))))))))))) (allB_succ 35 236 (allA_succ_of_accept 34 35
  236 (accept_3_2 34 35 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 35 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 35 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 236 (accept_3_2 31 35 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 35 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 236 (Polychromatic418967fa.accept_10_9_5_6_1_691
  29 35 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 236 (accept_3_2 28
  35 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 35 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 236 (accept_3_2 25 35 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 35 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 23
  35 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 236 (accept_3_2 22 35
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 236 (Polychromatic418967fa.accept_6_3_5_2_1_12
  21 35 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 236
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 20 35 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 236 (accept_3_2 19 35 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 236 (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 35 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 236 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 35 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 236 (accept_3_2 16 35 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 35 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 236 (accept_3_2 13 35 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 35 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 236 (Polychromatic418967fa.accept_10_1_5_6_1_649 11 35 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 236 (accept_3_2 10 35 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 35 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 236
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 8 35 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 236 (accept_3_2 7 35 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  236 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 35 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 35 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 236 (accept_3_2 4 35 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  35 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 236 (accept_3_2 1 35 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 236))))))))))))))))))))))))))))))))))) (allB_succ 34 236
  (allA_of_3_0 34 34 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 236 (allA_succ_of_accept 32 33 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 33 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 236 (accept_3_2 31 33 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 33 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 236 (accept_3_2 28 33 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 236 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 33 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 33 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 236 (accept_3_2 25 33 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 236 (Polychromatic418967fa.accept_14_10_5_12_1_3995 24 33 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 33 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 236 (accept_3_2 22 33 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 33 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 236
  (Polychromatic418967fa.accept_16_4_1_12_1_1792 20 33 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 236 (accept_3_2 19 33 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 33 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 236 (accept_3_2 16 33 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 236 (Polychromatic418967fa.accept_21_15_12_5_1_9766 15 33 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 33 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 236 (accept_3_2 13 33 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 33 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 33 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 236 (accept_3_2 10 33 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 236 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 33 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 33 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 236 (accept_3_2 7 33 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  236 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 33 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 236 (accept_3_2 4 33 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 33 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 236 (Polychromatic418967fa.accept_16_2_1_12_1_3798
  2 33 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 236 (accept_3_2 1 33
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 236))))))))))))))))))))))))))))))))) (allB_succ 32 236
  (allA_succ_of_accept 31 32 236 (accept_3_2 31 32 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32
  236 2 15 16 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 32 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 32 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 32 236 4 7 8 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 32 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 32 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 236 2 13 16 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 236 (accept_3_2 25 32 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 236 4 6 8 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 32 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 236 2 11 16 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 32 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 236 4 5 8 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 236 (accept_3_2 19 32 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  236 2 9 16 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 32 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 236 4 4 8 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 32 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 236 2 7 16 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 236 (accept_3_2 13 32 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 236 4 3 8 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 32 236 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 32 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 236 2 5 16 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 32 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 236 4 2 8 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 236 (accept_3_2 7 32 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 236
  2 3 16 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  236 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 32 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 32 236 4 1 8 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 32 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 32 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 236 2 1 16 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 236 (accept_3_2 1 32 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 32 236)))))))))))))))))))))))))))))))) (allB_succ 31 236 (allA_of_3_0 31 31 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 236 (allA_succ_of_accept 29 30 236
  (Polychromatic418967fa.accept_19_10_11_8_1_10121 29 30 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 30 236 2 14 15 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 30 236 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 30 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 236 2 13 15 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 236 (accept_3_2 25 30 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 236 2 12 15 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 30 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 30 236 2 11 15 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 30 236 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 30 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 236 2 10 15 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 236 (accept_3_2 19 30 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 236 2 9 15 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 17
  30 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 236 2 8 15 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 236
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 30 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 30 236 2 7 15 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 30 236 (accept_3_2 13 30 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30
  236 2 6 15 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  30 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 30 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 30 236 2 5 15 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 30 236 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 30 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 236 2 4 15 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 236 (accept_3_2 7 30 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 236 2 3 15 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 30 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 236 2 2 15 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 30 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 30 236 2 1 15 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 236 (accept_3_2 1 30 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30
  236)))))))))))))))))))))))))))))) (allB_succ 29 236 (allA_succ_of_accept 28 29 236 (accept_3_2 28 29 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 29 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 29 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 236 (accept_3_2 25 29 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 29 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 236 (Polychromatic418967fa.accept_10_3_9_6_1_94 23 29 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 236 (accept_3_2 22 29 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 29 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 29 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 236 (accept_3_2 19 29 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 29 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 29 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 236 (accept_3_2 16 29 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 29 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 29 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 236 (accept_3_2 13 29 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 236 (Polychromatic418967fa.accept_13_12_3_2_1_1470 12 29 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 29 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 236 (accept_3_2 10 29 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 236
  (Polychromatic418967fa.accept_16_8_13_12_1_3809 8 29 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 236 (accept_3_2 7 29 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  236 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 29 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 236 (Polychromatic418967fa.accept_10_5_9_6_1_697 5 29 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 236 (accept_3_2 4 29 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 29 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  29 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 236 (accept_3_2 1 29 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 236))))))))))))))))))))))))))))) (allB_succ 28 236 (allA_of_3_0
  28 28 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 236 (allA_succ_of_accept 26 27 236
  (Polychromatic418967fa.accept_16_10_11_12_1_4835 26 27 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 27 236 (accept_3_2 25 27 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 27 236 (Polychromatic418967fa.accept_16_8_11_12_1_962 24 27 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 236 (accept_3_2 22 27 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 236 (Polychromatic418967fa.accept_10_1_7_6_1_91 21
  27 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 236
  (Polychromatic418967fa.accept_14_6_13_12_1_810 20 27 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 236 (accept_3_2 19 27 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 27 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 27 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 236 (accept_3_2 16 27 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 27 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 236
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 27 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 27 236 (accept_3_2 13 27 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 27 236 (Polychromatic418967fa.accept_13_12_1_2_1_845 12 27 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 236 (accept_3_2 10 27 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 236 (Polychromatic418967fa.accept_13_9_1_2_1_2952 9
  27 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 27 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 236 (accept_3_2 7 27 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  236 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 27 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 27 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 236 (accept_3_2 4 27 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 236 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 27 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 236 (Polychromatic418967fa.accept_17_2_10_15_1_1238
  2 27 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 236 (accept_3_2 1 27
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 236))))))))))))))))))))))))))) (allB_succ 26 236
  (allA_succ_of_accept 25 26 236 (accept_3_2 25 26 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  236 2 12 13 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  23 26 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 26 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 236 2 11 13 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 26 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 236 2 10 13 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 236 (accept_3_2 19 26 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 236 2 9 13 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 236
  (Polychromatic418967fa.accept_12_5_2_8_1_172 17 26 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 26 236 2 8 13 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 26 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 26 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 26 236 2 7 13 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 26 236 (accept_3_2 13 26 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 236 2 6 13 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 26 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 26 236 2 5 13 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 26 236
  (Polychromatic418967fa.accept_19_9_7_8_1_3214 9 26 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 26 236 2 4 13 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 26 236 (accept_3_2 7 26 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 236
  2 3 13 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26
  236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 26 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 26 236 2 2 13 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 26 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 26 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 236 2 1 13 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 236 (accept_3_2 1 26 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 236)))))))))))))))))))))))))) (allB_succ 25 236 (allA_of_3_0 25 25 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 24 236 (allA_succ_of_accept 23 24 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 24
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 236 2 11 12 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 24 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 236 4 5 6 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 236 (accept_3_2 19 24 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  236 2 9 12 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 24 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 236 4 4 6 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 24 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 236 2 7 12 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 236 (accept_3_2 13 24 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 236 4 3 6 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 236 (Polychromatic418967fa.accept_16_11_8_12_1_1767 11 24
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 236 2 5 12 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 24 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 236 4 2 6 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 236 (accept_3_2 7 24 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 236
  2 3 12 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  236 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 24 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 236 4 1 6 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 24 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 24 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 236 2 1 12 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 236 (accept_3_2 1 24 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 236)))))))))))))))))))))))) (allB_succ 23 236 (allA_succ_of_accept 22 23 236 (accept_3_2 22
  23 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 23 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 236 (Polychromatic418967fa.accept_15_5_8_11_1_2350 20 23 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 236 (accept_3_2 19 23 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 23 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 17
  23 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 236 (accept_3_2 16 23
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 236 (Polychromatic418967fa.accept_6_3_5_2_1_12
  15 23 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 236
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 23 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 236 (accept_3_2 13 23 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 23 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 23 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 236 (accept_3_2 10 23 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 23 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 23 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 236 (accept_3_2 7 23 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  236 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 23 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 236 (Polychromatic418967fa.accept_13_5_10_2_1_856 5 23 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 236 (accept_3_2 4 23 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  23 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 236 (accept_3_2 1 23 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 236))))))))))))))))))))))) (allB_succ 22 236 (allA_of_3_0 22 22
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 236 (allA_succ_of_accept 20 21 236
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 21 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 236 (accept_3_2 19 21 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 21 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 236 (accept_3_2 16 21 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 21 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 21 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 236 (accept_3_2 13 21 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 21 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 21 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 236 (accept_3_2 10 21 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 21 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 21 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 236 (accept_3_2 7 21 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  236 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 21 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 236 (accept_3_2 4 21 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 236 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 21 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 2
  21 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 236 (accept_3_2 1 21 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 236))))))))))))))))))))) (allB_succ 20 236 (allA_succ_of_accept
  19 20 236 (accept_3_2 19 20 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 236 2 9 10 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 236
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 20 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 236 4 4 5 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 20 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 236 2 7 10 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 236 (accept_3_2 13 20 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 236 4 3 5 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 20 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 20 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 236 2 5 10 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 236
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 20 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 236 4 2 5 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 236 (accept_3_2 7 20 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 236
  2 3 10 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  236 (Polychromatic418967fa.accept_13_5_7_2_1_852 5 20 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 236 4 1 5 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 236 (Polychromatic418967fa.accept_16_3_4_12_1_3799 3 20 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 236 2 1 10 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 236 (accept_3_2 1 20 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 236)))))))))))))))))))) (allB_succ 19 236 (allA_of_3_0 19 19 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 236 (allA_succ_of_accept 17 18 236 (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 18 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 236 2 8 9 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 18 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 236 2 7 9 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 236 (accept_3_2 13 18 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  236 2 6 9 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 236 (Polychromatic418967fa.accept_19_11_18_8_1_5911 11 18 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 236 2 5 9 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 18 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 236 2 4 9 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 236 (accept_3_2 7 18 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 236 2 3 9 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 236 (Polychromatic418967fa.accept_20_5_18_16_1_1558 5 18 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 236 2 2 9 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 236
  (Polychromatic418967fa.accept_10_3_8_6_1_326 3 18 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 236 2 1 9 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 236 (accept_3_2 1 18 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  236)))))))))))))))))) (allB_succ 17 236 (allA_succ_of_accept 16 17 236 (accept_3_2 16 17 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 17 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 17 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 236 (accept_3_2 13 17 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 17 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 236 (Polychromatic418967fa.accept_10_1_7_6_1_91 11 17 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 236 (accept_3_2 10 17 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 17 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 236 (accept_3_2 7 17 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  236 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 17 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 17 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 236 (accept_3_2 4 17 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 17 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 17
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 236 (accept_3_2 1 17 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 236))))))))))))))))) (allB_succ 16 236 (allA_of_3_0 16 16 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 236 (allA_succ_of_accept 14 15 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 15 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 236 (accept_3_2 13 15 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 15 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 236 (accept_3_2 10 15 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 236 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 15 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 15 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 236 (accept_3_2 7 15 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  236 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 15 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 15 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 236 (accept_3_2 4 15 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 15 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 236 (Polychromatic418967fa.accept_16_2_15_12_1_1744
  2 15 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 236 (accept_3_2 1 15
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 236))))))))))))))) (allB_succ 14 236 (allA_succ_of_accept 13
  14 236 (accept_3_2 13 14 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 236 2 6 7 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 236
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 14 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 236 2 5 7 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 236 (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 14 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 236 2 4 7 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 236 (accept_3_2 7 14 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 236 2 3 7 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 14 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 236 2 2 7 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 14
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 236 2 1 7 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 236 (accept_3_2 1 14
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 236)))))))))))))) (allB_succ 13 236 (allA_of_3_0 13 13 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 236 (allA_succ_of_accept 11 12 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 11 12 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 236 2 5 6 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 236 (Polychromatic418967fa.accept_21_9_12_5_1_317 9 12 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 236 4 2 3 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 236 (accept_3_2 7 12 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 236 2 3 6 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 12 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 236 4 1 3 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 236 (Polychromatic418967fa.accept_13_3_12_2_1_385 3
  12 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 236 2 1 6 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 236 (accept_3_2 1 12
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 236)))))))))))) (allB_succ 11 236 (allA_succ_of_accept 10 11
  236 (accept_3_2 10 11 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 11 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 11 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 236 (accept_3_2 7 11 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 11 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 236 (Polychromatic418967fa.accept_10_5_1_6_1_672 5
  11 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 236 (accept_3_2 4 11 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 11 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 236 (accept_3_2 1 11 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  236))))))))))) (allB_succ 10 236 (allA_of_3_0 10 10 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 236
  (allA_succ_of_accept 8 9 236 (Polychromatic418967fa.accept_16_8_9_12_1_1737 8 9 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 236 (accept_3_2 7 9 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 9 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 236 (accept_3_2 4 9 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 9
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 236
  (Polychromatic418967fa.accept_15_2_9_11_1_1551 2 9 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 236 (accept_3_2 1 9 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 236)))))))))
  (allB_succ 8 236 (allA_succ_of_accept 7 8 236 (accept_3_2 7 8 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 236 2 3 4 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 8 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 236 4 1 2 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 8 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 236 2 1 4 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 236 (accept_3_2 1 8 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 236)))))))) (allB_succ 7 236 (allA_of_3_0 7 7 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 6 236 (allA_succ_of_accept 5 6 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 6 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 236 2 2 3 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 6 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 236 2 1 3 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 236 (accept_3_2 1 6 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 236))))))
  (allB_succ 5 236 (allA_succ_of_accept 4 5 236 (accept_3_2 4 5 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 5 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 5 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 236 (accept_3_2 1 5 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 236))))) (allB_succ 4 236 (allA_of_3_0 4 4 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 236 (allA_succ_of_accept 2 3 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 3 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 236 (accept_3_2 1 3 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 236))) (allB_succ 2 236 (allA_succ_of_accept 1 2 236 (accept_3_2 1 2 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 236)) (allB_two
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


