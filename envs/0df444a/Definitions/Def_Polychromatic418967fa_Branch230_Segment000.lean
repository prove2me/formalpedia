-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch230_Segment000
-- name    : Polychromatic418967fa_Branch230_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:36:38.641193+00:00
-- url     : https://prove2.me/theorems/c63d5378-2b6b-4aa1-8deb-4f0f4934745b
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

def Polychromatic418967fa.branch_230_segment_000 : allB 125 230 :=
  allB_succ' 107 124 230 (Eq.refl Bool.true) (allA_of_3_0 107 124 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 108 123 230 (Eq.refl Bool.true) (allA_succ_of_accept 107 123 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 123 230 (accept_3_2 106 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 123 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 123 230 (Polychromatic418967fa.accept_17_2_4_9_1_2791 104 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 123 230 (accept_3_2 103 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 123 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 102 123
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 123 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 123 230 (accept_3_2 100 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 123 230 (Polychromatic418967fa.accept_15_9_3_5_1_2077 99 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 123 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 98 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 230 (accept_3_2 97 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 123 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 96 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 123 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 123 230 (accept_3_2 94 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 123 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 123 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 92 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 230 (accept_3_2 91 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 123 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 90 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 123 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 123 230 (accept_3_2 88 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 123 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 123 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 86 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 230 (accept_3_2 85 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 123 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 123 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 123 230 (accept_3_2 82 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 123 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 123 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 80 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 230 (accept_3_2 79 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 123 230 (Polychromatic418967fa.accept_11_1_2_10_1_1426 78 123 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 123 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 123 230 (accept_3_2 76 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 123 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 123 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 74 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 230 (accept_3_2 73 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 123 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 123 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 123 230 (accept_3_2 70 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 123 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 123 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 68 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 230 (accept_3_2 67 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 123 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 123 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 123 230 (accept_3_2 64 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 123 230 (Polychromatic418967fa.accept_17_12_4_9_1_3889 63 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 123 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 62 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 230 (accept_3_2 61 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 230 (Polychromatic418967fa.accept_25_10_23_5_1_6517 60 123 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 123 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 123 230 (accept_3_2 58 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 123 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 123 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 230 (accept_3_2 55 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 123 230 (accept_3_2 52 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 123 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 123 230 (Polychromatic418967fa.accept_16_2_11_6_1_737 50 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 230 (accept_3_2 49 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 123 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 123 230 (accept_3_2 46 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 123 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 123 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 230 (accept_3_2 43 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 123 230 (accept_3_2 40 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 123 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 123 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 230 (accept_3_2 37 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 230 (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 123 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 230 (accept_3_2 34 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 230 (Polychromatic418967fa.accept_15_2_3_5_1_2991 32 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 230 (accept_3_2 31 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 123 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 230 (accept_3_2 28 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 230 (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 230 (accept_3_2 25 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 230 (accept_3_2 22 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 230 (accept_3_2 19 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 230 (accept_3_2 16 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 230 (Polychromatic418967fa.accept_13_2_6_9_1_2636 15 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 230 (Polychromatic418967fa.accept_13_1_6_9_1_1197 14 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 230 (accept_3_2 13 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 123 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 230 (accept_3_2 10 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 230 (accept_3_2 7 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 123 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 230 (accept_3_2 4 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 123 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 230 (accept_3_2 1 123 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 122 230 (Eq.refl Bool.true) (allA_succ_of_gcd 108 122 230 2 54 61 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 122 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 107 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 122 230 2 53 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 122 230 (Polychromatic418967fa.accept_13_1_5_9_1_226 105 122 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 122 230 2 52 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 122 230 (accept_3_2 103 122 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 122 230 2 51 61 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 122 230
  (Polychromatic418967fa.accept_11_2_1_10_1_196 101 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 122 230 2 50 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 122 230 (Polychromatic418967fa.accept_22_11_12_10_1_1424 99 122 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 122 230 2 49 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 122 230 (accept_3_2 97 122 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 122 230 2 48 61 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 122 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 95 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 122 230 2 47 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 122 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 122 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 122 230 2 46 61 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 122 230 (accept_3_2 91 122 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 122 230 2 45 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 122 230 (Polychromatic418967fa.accept_15_14_2_5_1_1272
  89 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 122 230 2 44 61 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 122 230
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 87 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 122 230 2 43 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 122 230 (accept_3_2 85 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 122 230 2 42 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 122 230 (Polychromatic418967fa.accept_20_3_2_10_1_3579 83 122 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 122 230 2 41 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 122 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 81 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 122 230 2 40 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 122 230 (accept_3_2 79 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 122 230 2 39 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 122 230 (Polychromatic418967fa.accept_19_1_8_2_1_2876 77 122 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 122 230 2 38 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 122 230
  (Polychromatic418967fa.accept_11_9_1_10_1_920 75 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 122 230 2 37 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 122 230 (accept_3_2 73 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 122 230 2 36 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 122 230 (Polychromatic418967fa.accept_15_11_2_5_1_2076 71 122 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 122 230 2 35 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 122 230
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 69 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 122 230 2 34 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 122 230 (accept_3_2 67 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 122 230 2 33 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 122 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 122 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 122 230 2 32 61 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 230
  (Polychromatic418967fa.accept_15_3_2_5_1_2980 63 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 122 230 2 31 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 122 230 (accept_3_2 61 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 230 2 30 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 230 (Polychromatic418967fa.accept_14_3_10_6_1_1136 59 122 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 230 2 29 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 230
  (Polychromatic418967fa.accept_11_2_1_10_1_196 57 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 230 2 28 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 230 (accept_3_2 55 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 230 2 27 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 122 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 230 2 26 61 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 230 2 25 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 230 (accept_3_2 49 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 230 2 24 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 230 (Polychromatic418967fa.accept_26_21_18_22_1_13745 47 122 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 230 2 23 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 230
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 230 2 22 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 230 (accept_3_2 43 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 230 2 21 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 230 (Polychromatic418967fa.accept_13_2_5_9_1_610 41 122 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 230 2 20 61 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 230 2 19 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 230 (accept_3_2 37 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 230 2 18 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 230 (Polychromatic418967fa.accept_11_2_1_10_1_196 35 122 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 230 2 17 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 230
  (Polychromatic418967fa.accept_15_3_2_5_1_2980 33 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 230 2 16 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 230 (accept_3_2 31 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 230 2 15 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 230 (Polychromatic418967fa.accept_13_3_5_9_1_5285 29 122 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 230 2 14 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 230
  (Polychromatic418967fa.accept_13_1_5_9_1_226 27 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 230 2 13 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 230 (accept_3_2 25 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 230 2 12 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 122 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 230 2 11 61 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 230
  (Polychromatic418967fa.accept_26_21_18_22_1_13745 21 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 122 230 2 10 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 122 230 (accept_3_2 19 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 230 2 9 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 122 230 (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 122 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 230 2 8 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 230
  (Polychromatic418967fa.accept_13_2_5_9_1_610 15 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 122 230 2 7 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 122 230 (accept_3_2 13 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 122 230 2 6 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 122 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 122 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 122 230 2 5 61 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 122 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 122 230 2 4 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 122 230 (accept_3_2 7 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122
  230 2 3 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  122 230 (Polychromatic418967fa.accept_19_5_8_2_1_1707 5 122 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 122 230 2 2 61 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 122 230 (Polychromatic418967fa.accept_13_3_5_9_1_5285 3 122 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 230 2 1 61 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 230 (accept_3_2 1 122 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 121 230 (Eq.refl Bool.true) (allA_of_3_0 110 121 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 111 120 230 (Eq.refl Bool.true) (allA_succ_of_gcd 110 120 230 10 11 12 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 120 230 (accept_3_2 109 120 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 120 230 2 54 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 120 230 (Polychromatic418967fa.accept_7_2_1_6_1_173
  107 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 120 230 2 53 60 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 120 230 5 21 24
  46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 120 230 2 52
  60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 120
  230 (accept_3_2 103 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 120 230 2 51 60 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 120 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 101 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 120 230 10 10 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 120 230 (Polychromatic418967fa.accept_13_8_3_9_1_5269 99 120 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 120 230 2 49 60 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 120 230 (accept_3_2 97 120 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 120 230 2 48 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 120 230 5 19 24 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 94 120 230 2 47 60 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 120 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 93 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 120 230 2 46 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 120 230 (accept_3_2 91 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 120 230 10 9 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 120 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 120 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 120 230 2 44 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 120 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 87 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 120 230 2 43 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 85 120 230 5 17 24 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 120 230 2 42 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 120 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 83 120 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 120 230 2 41 60 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 120 230
  (Polychromatic418967fa.accept_21_18_15_20_1_6076 81 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 120 230 10 8 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 120 230 (accept_3_2 79 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 120 230 2 39 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 120 230 (Polychromatic418967fa.accept_13_12_3_9_1_4341 77 120 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 120 230 2 38 60 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 120 230 5 15 24 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 120 230 2 37 60 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 120 230
  (accept_3_2 73 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 120 230 2 36 60 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 120 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 71 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 120 230 10 7 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 120 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 120 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 120 230 2 34 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 120 230 (accept_3_2 67 120 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 120 230 2 33 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 120 230 5 13 24 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 120 230 2 32 60 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 120 230
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 63 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 120 230 2 31 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 120 230 (accept_3_2 61 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 230 10 6 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 230 (Polychromatic418967fa.accept_13_7_3_9_1_1142 59 120 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 230 2 29 60 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 120 230
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 57 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 120 230 2 28 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 120 230 5 11 24 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 120 230 2 27 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 120 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 120 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 230 2 26 60 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 120 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 120 230 10 5 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 120 230 (accept_3_2 49 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 230 2 24 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 120 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 230 2 23 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 120 230 5 9 24 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 120 230 2 22 60 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 230 (accept_3_2 43 120 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 230 2 21 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 230
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 41 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 230 10 4 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 120 230 (Polychromatic418967fa.accept_18_3_12_14_1_2232 39 120 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 120 230 2 19 60 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 230 (accept_3_2 37 120 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 230 2 18 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 120 230 5 7 24 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 120 230 2 17 60 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 120 230 2 16 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 120 230 (accept_3_2 31 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 230 10 3 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 120 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 120 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 230 2 14 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 120 230
  (Polychromatic418967fa.accept_17_10_1_9_1_11372 27 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 120 230 2 13 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 120 230 5 5 24 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 120 230 2 12 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 120 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 230 2 11 60 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 230
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 21 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 230 10 2 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 120 230 (accept_3_2 19 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 230 2 9 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 120 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 120 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 230 2 8 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 120 230 5 3 24 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 120 230 2 7 60 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 230 (accept_3_2 13 120 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 230 2 6 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 120 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 230 10 1 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 120 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 120 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 120 230 2 4 60 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 230 (accept_3_2 7 120 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 230 2 3 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 120 230 5 1 24 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 120 230 2 2 60 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 120 230 (Polychromatic418967fa.accept_17_3_1_9_1_9012 3
  120 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 230 2 1 60 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 230 (accept_3_2 1
  120 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 119 230 (Eq.refl Bool.true) (allA_succ_of_accept 111 119 230
  (Polychromatic418967fa.accept_6_3_5_2_1_12 111 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 119 230 (Polychromatic418967fa.accept_13_6_2_9_1_1188 110 119 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 119 230 (accept_3_2 109 119 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 119 230 (Polychromatic418967fa.accept_34_6_17_26_1_13744 108 119 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 119 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 107 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 119 230 (accept_3_2 106 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 119 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 119 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 104 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 119 230 (accept_3_2 103 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 119 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 102 119
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 119 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 119 230 (accept_3_2 100 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 119 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 119 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 98 119 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 119 230 (accept_3_2 97 119 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 119 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 96 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 119 230
  (Polychromatic418967fa.accept_16_15_7_6_1_1453 95 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 119 230 (accept_3_2 94 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 119 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 119 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 92 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 119 230 (accept_3_2 91 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 119 230 (Polychromatic418967fa.accept_19_14_5_2_1_6941 90 119
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 119 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 119 230 (accept_3_2 88 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 119 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 119 230 (Polychromatic418967fa.accept_19_10_5_2_1_9784 86 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 119 230 (accept_3_2 85 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 119 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 119 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 119 230
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 83 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 119 230 (accept_3_2 82 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 119 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 119 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 119 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 119 230 (accept_3_2 79 119 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 119 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 119 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 119 230 (accept_3_2 76 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 119 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 119 230 (Polychromatic418967fa.accept_11_8_9_10_1_503 74 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 119 230 (accept_3_2 73 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 119 230 (Polychromatic418967fa.accept_13_7_2_9_1_1826 72 119
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 119 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 119 230 (accept_3_2 70 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 119 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 119 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 119 230 (accept_3_2 67 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 119 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 119 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 119 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 119 230 (accept_3_2 64 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 119 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 119 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 119 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 230 (accept_3_2 61 119 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 119 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 230
  (Polychromatic418967fa.accept_13_7_2_9_1_1826 59 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 119 230 (accept_3_2 58 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 119 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 119 230 (Polychromatic418967fa.accept_11_1_9_10_1_184 56 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 119 230 (accept_3_2 55 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 230 (Polychromatic418967fa.accept_15_9_14_5_1_2086 54 119
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 119 230 (accept_3_2 52 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 119 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 119 230 (Polychromatic418967fa.accept_13_11_2_9_1_2640 50 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 119 230 (accept_3_2 49 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 119 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 119 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 230
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 47 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 119 230 (accept_3_2 46 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 119 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 119 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 119 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 230 (accept_3_2 43 119 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 119 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 119 230 (accept_3_2 40 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 119 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 119 230 (Polychromatic418967fa.accept_15_8_14_5_1_2089 38 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 230 (accept_3_2 37 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 230 (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 119
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 119 230 (accept_3_2 34 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 119 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 230 (accept_3_2 31 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 119 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 119 230 (accept_3_2 28 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 119 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 119 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 119 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 230 (accept_3_2 25 119 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 230
  (Polychromatic418967fa.accept_11_1_9_10_1_184 23 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 230 (accept_3_2 22 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 119 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 230 (accept_3_2 19 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 230 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 119
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 230 (accept_3_2 16 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 119 230 (Polychromatic418967fa.accept_13_1_2_9_1_1186 14 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 230 (accept_3_2 13 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 119 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 230
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 119 230 (accept_3_2 10 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  119 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 119 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 119 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 230 (accept_3_2 7 119 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 230 (accept_3_2 4 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 230 (Polychromatic418967fa.accept_15_2_14_5_1_2072 2 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 230 (accept_3_2 1 119 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 119
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 118 230 (Eq.refl Bool.true) (allA_of_3_0 113 118 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 114 117 230 (Eq.refl Bool.true) (allA_succ_of_accept 113 117 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 117 230 (accept_3_2 112 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 117 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 117 230 (Polychromatic418967fa.accept_25_10_17_5_1_6511 110 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 230 (accept_3_2 109 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 230 (Polychromatic418967fa.accept_17_6_15_9_1_1791 108
  117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 117 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 107 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 230 (accept_3_2 106 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 117 230 (Polychromatic418967fa.accept_20_5_17_10_1_3632 105 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 230 (Polychromatic418967fa.accept_22_16_7_10_1_7356 104 117 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 230 (accept_3_2 103 117 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 230 (Polychromatic418967fa.accept_7_4_5_6_1_344
  102 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 117 230 (accept_3_2 100 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 117 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 117 230 (Polychromatic418967fa.accept_15_8_12_5_1_2987 98 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 230 (accept_3_2 97 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 230 (Polychromatic418967fa.accept_15_6_12_5_1_2108 96 117
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 117 230 (accept_3_2 94 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 117 230 (Polychromatic418967fa.accept_18_3_9_14_1_2219 93 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 117 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 92 117 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 230 (accept_3_2 91 117 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 117 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 90 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 117 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 117 230 (accept_3_2 88 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 117 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 117 230 (Polychromatic418967fa.accept_17_1_15_9_1_1743 86 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 230 (accept_3_2 85 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 230 (Polychromatic418967fa.accept_15_9_12_5_1_1267 84 117
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 117 230 (accept_3_2 82 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 117 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 117 230 (Polychromatic418967fa.accept_11_3_7_10_1_180 80 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 230 (accept_3_2 79 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 117 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 117 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 230 (accept_3_2 76 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 117 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 117 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 74 117 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 230 (accept_3_2 73 117 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 230 (Polychromatic418967fa.accept_21_9_12_20_1_10792 72 117 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 117 230 (accept_3_2 70 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 117 230 (Polychromatic418967fa.accept_11_3_7_10_1_180 69 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 117 230 (Polychromatic418967fa.accept_15_8_12_5_1_2987 68 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 230 (accept_3_2 67 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 66 117
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 117 230 (accept_3_2 64 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 117 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 117 230 (Polychromatic418967fa.accept_15_2_12_5_1_2107 62 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 230 (accept_3_2 61 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 117 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 230 (accept_3_2 58 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 117 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 117 230 (Polychromatic418967fa.accept_19_18_3_2_1_6939 56 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 230 (accept_3_2 55 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 117
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 117 230 (accept_3_2 52 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 117 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 117 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 117 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 230 (accept_3_2 49 117 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 230 (Polychromatic418967fa.accept_20_8_17_10_1_8016 48 117 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 230 (accept_3_2 46 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 230 (Polychromatic418967fa.accept_20_5_17_10_1_3632 45 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 230 (Polychromatic418967fa.accept_19_6_3_2_1_4119 44 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 230 (accept_3_2 43 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 117
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 230 (accept_3_2 40 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 117 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 117 230 (Polychromatic418967fa.accept_15_8_12_5_1_2987 38 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 230 (accept_3_2 37 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 117 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 230 (accept_3_2 34 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 117 230 (Polychromatic418967fa.accept_16_1_5_6_1_4435 33 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 117 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 230 (accept_3_2 31 117 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 230 (accept_3_2 28 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 117 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 117 230 (Polychromatic418967fa.accept_22_4_7_10_1_12171 26 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 230 (accept_3_2 25 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 230 (Polychromatic418967fa.accept_15_9_12_5_1_1267 24 117
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 230 (accept_3_2 22 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 117 230 (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 230 (Polychromatic418967fa.accept_16_4_5_6_1_8071 20 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 230 (accept_3_2 19 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 117 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 230 (accept_3_2 16 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 117 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 117 230 (Polychromatic418967fa.accept_11_3_7_10_1_180 14 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 230 (accept_3_2 13 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 230 (Polychromatic418967fa.accept_19_12_3_2_1_12509 12 117
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 230 (accept_3_2 10 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  117 230 (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 117 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 117 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 230 (accept_3_2 7 117 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 230 (accept_3_2 4 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 117 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 230 (Polychromatic418967fa.accept_15_2_12_5_1_2107 2 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 230 (accept_3_2 1 117 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 115 116 230 (Eq.refl Bool.true) (allA_succ_of_gcd 114 116 230 2 57 58 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 116 230
  (Polychromatic418967fa.accept_12_5_8_2_1_309 113 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 116 230 2 56 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 116 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 111 116 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 116 230 2 55 58 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 116 230 (accept_3_2 109 116 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 116 230 2 54 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 116 230 (Polychromatic418967fa.accept_7_2_4_6_1_166
  107 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 116 230 2 53 58 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 116 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 105 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 116 230 2 52 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 116 230 (accept_3_2 103 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 116 230 2 51 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 116 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 101 116 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 116 230 2 50 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 116 230
  (Polychromatic418967fa.accept_13_8_12_9_1_1168 99 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 116 230 2 49 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 116 230 (accept_3_2 97 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 116 230 2 48 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 116 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 95 116 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 116 230 2 47 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 116 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 93 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 116 230 2 46 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 116 230 (accept_3_2 91 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 116 230 2 45 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 116 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 89 116 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 116 230 2 44 58 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 116 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 87 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 116 230 2 43 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 116 230 (accept_3_2 85 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 116 230 2 42 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 116 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 83 116 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 116 230 2 41 58 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 116 230
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 81 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 116 230 2 40 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 116 230 (accept_3_2 79 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 116 230 2 39 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 116 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 116 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 116 230 2 38 58 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 116 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 116 230 2 37 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 116 230 (accept_3_2 73 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 116 230 2 36 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 116 230 (Polychromatic418967fa.accept_11_5_6_10_1_1432 71 116 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 116 230 2 35 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 116 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 69 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 116 230 2 34 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 116 230 (accept_3_2 67 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 116 230 2 33 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 116 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 65 116 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 116 230 2 32 58 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 116 230
  (Polychromatic418967fa.accept_17_12_14_9_1_5079 63 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 116 230 2 31 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 116 230 (accept_3_2 61 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 116 230 2 30 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 116 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 230 2 29 58 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 230 2 28 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 230 (accept_3_2 55 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 230 2 27 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 116 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 230 2 26 58 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 230 2 25 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 230 (accept_3_2 49 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 230 2 24 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 116 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 230 2 23 58 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 230 2 22 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 230 (accept_3_2 43 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 230 2 21 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 116 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 230 2 20 58 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 230 2 19 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 230 (accept_3_2 37 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 230 2 18 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 116 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 116 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 230 2 17 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 116 230 2 16 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 116 230 (accept_3_2 31 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 116 230 2 15 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 116 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 116 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 230 2 14 58 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 230
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 116 230 2 13 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 116 230 (accept_3_2 25 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 116 230 2 12 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 116 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 116 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 230 2 11 58 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 230 2 10 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 116 230 (accept_3_2 19 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 116 230 2 9 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 116 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 116 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 230 2 8 58 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 116 230 2 7 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 116 230 (accept_3_2 13 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 116 230 2 6 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 116 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 116 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 116 230 2 5 58 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 116 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 116 230 2 4 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 116 230 (accept_3_2 7 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116
  230 2 3 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  116 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 116 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 116 230 2 2 58 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 116 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 116 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 230 2 1 58 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 230 (accept_3_2 1 116 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 230 (allA_of_3_0 115 115 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 114 230
  (allA_succ_of_accept 113 114 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 113 114 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 114 230 2 56 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 114 230 (Polychromatic418967fa.accept_9_3_6_5_1_63
  111 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 114 230 2 55 57 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 114 230
  (accept_3_2 109 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 114 230 2 54 57 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 114 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 107 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 114 230 2 53 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 114 230 (Polychromatic418967fa.accept_12_9_6_2_1_1273 105 114 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 114 230 2 52 57 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 114 230 (accept_3_2 103 114 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 114 230 2 51 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 114 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 101 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 114 230 2 50 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 114 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 99 114 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 114 230 2 49 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 114 230 (accept_3_2 97 114 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 114 230 2 48 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 114 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 95
  114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 114 230 2 47 57 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 114 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 93 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 114 230 2 46 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 114 230 (accept_3_2 91 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 230 2 45 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 89 114 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 114 230 2 44 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 114 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 87 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 114 230 2 43 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 114 230 (accept_3_2 85 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 230 2 42 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 83 114 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 114 230 2 41 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 114 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 81 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 114 230 2 40 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 114 230 (accept_3_2 79 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 230 2 39 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 230 (Polychromatic418967fa.accept_13_12_10_9_1_1166 77 114 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 114 230 2 38 57 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 114 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 75 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 114 230 2 37 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 114 230 (accept_3_2 73 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 230 2 36 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 114 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 114 230 2 35 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 114 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 69 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 114 230 2 34 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 114 230 (accept_3_2 67 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 230 2 33 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 114 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 230 2 32 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 114 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 114 230 2 31 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 114 230 (accept_3_2 61 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 230 2 30 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 114 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 230 2 29 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 114 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 114 230 2 28 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 114 230 (accept_3_2 55 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 230 2 27 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 114 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 230 2 26 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 114 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 114 230 2 25 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 114 230 (accept_3_2 49 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 230 2 24 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 114 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 230 2 23 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 114 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 114 230 2 22 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 114 230 (accept_3_2 43 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 230 2 21 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 230 (Polychromatic418967fa.accept_15_11_9_5_1_2974 41 114 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 230 2 20 57 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 114 230 2 19 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 230 (accept_3_2 37 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 230 2 18 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 114 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 230 2 17 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 230 2 16 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 230 (accept_3_2 31 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 230 2 15 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 114 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 230 2 14 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 230
  (Polychromatic418967fa.accept_11_5_4_10_1_524 27 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 114 230 2 13 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 114 230 (accept_3_2 25 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 230 2 12 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 230 (Polychromatic418967fa.accept_21_2_9_20_1_9260 23 114 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 230 2 11 57 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 230 2 10 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 114 230 (accept_3_2 19 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 230 2 9 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 114 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 114 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 230 2 8 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 114 230 2 7 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 114 230 (accept_3_2 13 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 230 2 6 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 114 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 114 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 230 2 5 57 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 230 2 4 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 230 (accept_3_2 7 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114
  230 2 3 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  114 230 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 114 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 230 2 2 57 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 114 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 114 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 230 2 1 57 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 230 (accept_3_2 1 114 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 230 (allA_succ_of_accept 112 113 230 (accept_3_2 112 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 113 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 110 113
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 230 (accept_3_2 109 113
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 230
  (Polychromatic418967fa.accept_15_3_8_5_1_2105 108 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 107 113 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 230 (accept_3_2 106 113 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 113 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 104 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 113 230 (accept_3_2 103 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 113 230 (Polychromatic418967fa.accept_15_12_8_5_1_5048 102 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 101 113 230 (Polychromatic418967fa.accept_15_11_8_5_1_1278 101 113 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 230 (accept_3_2 100 113 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 99
  113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 230
  (Polychromatic418967fa.accept_16_2_1_6_1_2342 98 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 230 (accept_3_2 97 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 96 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 95 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 230 (accept_3_2 94 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 92 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 113 230 (accept_3_2 91 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 113 230 (Polychromatic418967fa.accept_22_2_3_10_1_12183 90 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 113 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 230 (accept_3_2 88 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 86 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 230 (accept_3_2 85 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 230 (Polychromatic418967fa.accept_11_7_3_10_1_1461 84 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 230 (accept_3_2 82 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 80 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 230 (accept_3_2 79 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 230 (Polychromatic418967fa.accept_15_3_8_5_1_2105 78 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 230 (Polychromatic418967fa.accept_14_7_1_6_1_3514 77 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 230 (accept_3_2 76 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 113 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 230
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 74 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 230 (accept_3_2 73 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 230 (accept_3_2 70 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 68 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 230 (accept_3_2 67 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 230 (Polychromatic418967fa.accept_16_2_1_6_1_2342 66 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 230 (accept_3_2 64 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 230
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 62 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 230 (accept_3_2 61 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 230 (Polychromatic418967fa.accept_19_3_18_2_1_6935 60 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 230 (accept_3_2 58 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 230 (accept_3_2 55 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 230 (Polychromatic418967fa.accept_16_5_1_6_1_3367 53 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 230 (accept_3_2 52 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 113 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 230
  (Polychromatic418967fa.accept_16_2_1_6_1_2342 50 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 230 (accept_3_2 49 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 230 (Polychromatic418967fa.accept_15_3_8_5_1_2105 48 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 230 (accept_3_2 46 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 230 (accept_3_2 43 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 230 (Polychromatic418967fa.accept_15_12_8_5_1_5048 42 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 230 (Polychromatic418967fa.accept_15_11_8_5_1_1278 41 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 230 (accept_3_2 40 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 113 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 230
  (Polychromatic418967fa.accept_21_17_8_20_1_7805 38 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 113 230 (accept_3_2 37 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 113 230 (Polychromatic418967fa.accept_17_2_11_9_1_1739 36 113 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 113 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 230 (accept_3_2 34 113 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 230 (accept_3_2 31 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 230 (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 230 (accept_3_2 28 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 113 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 230 (accept_3_2 25 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 230 (Polychromatic418967fa.accept_19_5_18_2_1_5404 24 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 230 (accept_3_2 22 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 230 (accept_3_2 19 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 230 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 230 (Polychromatic418967fa.accept_20_17_13_10_1_5059 17 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 230 (accept_3_2 16 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 113 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 230
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 230 (accept_3_2 13 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 230 (accept_3_2 10 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 230 (accept_3_2 7 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 230 (Polychromatic418967fa.accept_22_6_3_10_1_12182 6 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 230 (accept_3_2 4 113 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 113 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 230 (accept_3_2 1 113 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 230 (allA_of_3_0 112 112 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 230
  (allA_succ_of_accept 110 111 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 110 111 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 230 (accept_3_2 109 111 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 111 230 (Polychromatic418967fa.accept_11_9_1_10_1_920 108 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 230 (accept_3_2 106 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 230 (Polychromatic418967fa.accept_15_14_6_5_1_7215 104 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 230 (accept_3_2 103 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 102 111
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 230 (accept_3_2 100 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 230 (Polychromatic418967fa.accept_13_8_7_9_1_611 99 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 98 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 230 (accept_3_2 97 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 96 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 230 (accept_3_2 94 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 92 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 230 (accept_3_2 91 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 230 (Polychromatic418967fa.accept_11_2_1_10_1_196 90 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 230 (accept_3_2 88 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 87 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 230 (Polychromatic418967fa.accept_11_9_1_10_1_920 86 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 230 (accept_3_2 85 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 230 (Polychromatic418967fa.accept_13_6_7_9_1_1848 84 111
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 230 (accept_3_2 82 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 111 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 111 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 80 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 230 (accept_3_2 79 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 230 (accept_3_2 76 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 111 230 (Polychromatic418967fa.accept_11_9_1_10_1_920 75 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 111 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 74 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 230 (accept_3_2 73 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 230 (Polychromatic418967fa.accept_15_12_6_5_1_1275 72 111 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 230 (accept_3_2 70 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 111 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 111 230 (Polychromatic418967fa.accept_11_2_1_10_1_196 68 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 230 (accept_3_2 67 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 66 111
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 230 (accept_3_2 64 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 230 (Polychromatic418967fa.accept_13_11_7_9_1_612 63 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 62 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 230 (accept_3_2 61 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 230 (accept_3_2 58 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 230 (accept_3_2 55 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 230 (accept_3_2 52 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 230 (Polychromatic418967fa.accept_13_11_7_9_1_612 50 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 230 (accept_3_2 49 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 230 (Polychromatic418967fa.accept_15_3_6_5_1_2079 48 111
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 230 (accept_3_2 46 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 230 (accept_3_2 43 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 230 (accept_3_2 40 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 230 (Polychromatic418967fa.accept_16_7_15_6_1_1428 39 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 230 (accept_3_2 37 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 230 (Polychromatic418967fa.accept_19_17_16_2_1_8390 36 111 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 230 (accept_3_2 34 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 230 (Polychromatic418967fa.accept_13_6_7_9_1_1848 32 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 230 (accept_3_2 31 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 111
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 230 (accept_3_2 28 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 230 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 230 (accept_3_2 25 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 230 (accept_3_2 22 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 230 (accept_3_2 19 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 230 (accept_3_2 16 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 230 (Polychromatic418967fa.accept_15_14_6_5_1_7215 14 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 230 (accept_3_2 13 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 230 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 111
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 230 (accept_3_2 10 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 230 (accept_3_2 7 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 111 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 230 (accept_3_2 4 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 230 (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 111 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 230 (accept_3_2 1 111 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 230 (allA_succ_of_accept 109 110 230 (accept_3_2 109 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 110 230 2 54 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 110 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 107 110 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 110 230 2 53 55 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 110 230 5 21 22 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 110 230 2 52 55 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 110 230
  (accept_3_2 103 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 110 230 2 51 55 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 110 230
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 101 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 110 230 10 10 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 110 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 99 110 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 110 230 2 49 55 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 110 230 (accept_3_2 97 110 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 110 230 2 48 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 110 230 5 19 22 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 94 110 230 2 47 55 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 110 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 93 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 110 230 2 46 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 110 230 (accept_3_2 91 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 110 230 10 9 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 110 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 89 110 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 110 230 2 44 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 110 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 87 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 110 230 2 43 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 85 110 230 5 17 22 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 110 230 2 42 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 110 230 (Polychromatic418967fa.accept_14_13_12_6_1_2735 83 110
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 110 230 2 41 55 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 110 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 81 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 110 230 10 8 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 110 230 (accept_3_2 79 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 110 230 2 39 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 110 230 (Polychromatic418967fa.accept_19_1_15_2_1_6950 77 110 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 110 230 2 38 55 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 110 230 5 15 22 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 110 230 2 37 55 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 110 230
  (accept_3_2 73 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 110 230 2 36 55 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 110 230
  (Polychromatic418967fa.accept_7_1_5_6_1_59 71 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 110 230 10 7 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 110 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 110 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 110 230 2 34 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 110 230 (accept_3_2 67 110 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 110 230 2 33 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 110 230 5 13 22 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 110 230 2 32 55 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 230
  (Polychromatic418967fa.accept_19_6_15_2_1_2857 63 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 110 230 2 31 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 110 230 (accept_3_2 61 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 230 10 6 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 230 (Polychromatic418967fa.accept_13_7_6_9_1_1831 59 110 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 230 2 29 55 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 230
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 230 2 28 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 110 230 5 11 22 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 110 230 2 27 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 110 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 110 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 230 2 26 55 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 230 10 5 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 230 (accept_3_2 49 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 230 2 24 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 230 (Polychromatic418967fa.accept_18_11_2_14_1_3351 47 110 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 230 2 23 55 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 110 230 5 9 22 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 110 230 2 22 55 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 110 230 (accept_3_2 43
  110 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 110 230 2 21 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 110 230
  (Polychromatic418967fa.accept_13_2_6_9_1_2636 41 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 110 230 10 4 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 110 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 110 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 110 230 2 19 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 110 230 (accept_3_2 37 110 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 110 230 2 18 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 110 230 5 7 22 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 110 230 2 17 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 230 2 16 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 230 (accept_3_2 31 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 230 10 3 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 110 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 230 2 14 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 230
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 230 2 13 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 110 230 5 5 22 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 110 230 2 12 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 110 230 (Polychromatic418967fa.accept_13_10_6_9_1_1152 23 110 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 230 2 11 55 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 230 10 2 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 230 (accept_3_2 19 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 230 2 9 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 110 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 110 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 230 2 8 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 110 230 5 3 22 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 110 230 2 7 55 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 230 (accept_3_2 13 110 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 230 2 6 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 110 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 110 230 10 1 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 110 230 (Polychromatic418967fa.accept_19_9_15_2_1_9758 9 110 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 230 2 4 55 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 230 (accept_3_2 7 110 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110 230 2 3 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 110 230 5 1 22 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 110 230 2 2 55 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 3
  110 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 230 2 1 55 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 230 (accept_3_2 1
  110 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 230 (allA_of_3_0 109 109 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 230
  (allA_succ_of_accept 107 108 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 107 108 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 108 230 2 53 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 108 230 (Polychromatic418967fa.accept_17_3_6_9_1_2761
  105 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 108 230 2 52 54 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 108 230
  (accept_3_2 103 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 108 230 2 51 54 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 108 230
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 101 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 108 230 2 50 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 108 230 (Polychromatic418967fa.accept_13_8_4_9_1_1145 99 108 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 108 230 2 49 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 108 230 (accept_3_2 97 108 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 108 230 2 48 54 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 108 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 95 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 108 230 2 47 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 108 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 108 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 108 230 2 46 54 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 108 230 (accept_3_2 91 108 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 108 230 2 45 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 108 230 (Polychromatic418967fa.accept_11_1_9_10_1_184
  89 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 108 230 2 44 54 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 108 230
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 87 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 108 230 2 43 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 108 230 (accept_3_2 85 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 230 2 42 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 230 (Polychromatic418967fa.accept_13_5_4_9_1_601 83 108 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 108 230 2 41 54 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 108 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 81 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 108 230 2 40 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 108 230 (accept_3_2 79 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 230 2 39 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 230 (Polychromatic418967fa.accept_15_2_3_5_1_2991 77 108 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 108 230 2 38 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 108 230
  (Polychromatic418967fa.accept_20_15_8_10_1_3602 75 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 108 230 2 37 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 108 230 (accept_3_2 73 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 230 2 36 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 230 (Polychromatic418967fa.accept_13_6_4_9_1_4326 71 108 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 230 2 35 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 108 230
  (Polychromatic418967fa.accept_15_9_3_5_1_2077 69 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 108 230 2 34 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 108 230 (accept_3_2 67 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 230 2 33 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 108 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 230 2 32 54 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 108 230
  (Polychromatic418967fa.accept_11_8_9_10_1_503 63 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 108 230 2 31 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 108 230 (accept_3_2 61 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 230 2 30 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 230 (Polychromatic418967fa.accept_13_7_4_9_1_1865 59 108 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 230 2 29 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 108 230
  (Polychromatic418967fa.accept_13_5_4_9_1_601 57 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 108 230 2 28 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 108 230 (accept_3_2 55 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 230 2 27 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 108 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 230 2 26 54 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 108 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 108 230 2 25 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 108 230 (accept_3_2 49 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 230 2 24 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 230 (Polychromatic418967fa.accept_13_8_4_9_1_1145 47 108 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 230 2 23 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 108 230
  (Polychromatic418967fa.accept_11_1_9_10_1_184 45 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 108 230 2 22 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 108 230 (accept_3_2 43 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 230 2 21 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 230 (Polychromatic418967fa.accept_11_8_9_10_1_503 41 108 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 230 2 20 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 108 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 108 230 2 19 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 108 230 (accept_3_2 37 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 230 2 18 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 108 230 (Polychromatic418967fa.accept_19_16_13_2_1_6920 35 108 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 230 2 17 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 230
  (Polychromatic418967fa.accept_13_7_4_9_1_1865 33 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 108 230 2 16 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 108 230 (accept_3_2 31 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 230 2 15 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 230 (Polychromatic418967fa.accept_19_10_13_2_1_9771 29 108 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 230 2 14 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 108 230
  (Polychromatic418967fa.accept_19_8_13_2_1_6921 27 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 108 230 2 13 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 108 230 (accept_3_2 25 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 230 2 12 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 108 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 108 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 230 2 11 54 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 230
  (Polychromatic418967fa.accept_13_8_4_9_1_1145 21 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 108 230 2 10 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 108 230 (accept_3_2 19 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 230 2 9 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 108 230 (Polychromatic418967fa.accept_14_3_10_6_1_1136 17 108 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 230 2 8 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 230
  (Polychromatic418967fa.accept_17_15_6_9_1_13743 15 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 108 230 2 7 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 108 230 (accept_3_2 13 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 230 2 6 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 108 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 108 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 230 2 5 54 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 108 230 2 4 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 108 230 (accept_3_2 7 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108
  230 2 3 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  108 230 (Polychromatic418967fa.accept_13_5_4_9_1_601 5 108 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 108 230 2 2 54 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 108 230 (Polychromatic418967fa.accept_14_3_10_6_1_1136 3 108 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 230 2 1 54 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 230 (accept_3_2 1 108 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 230 (allA_succ_of_accept 106 107 230 (accept_3_2 106 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 107 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 104
  107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 230 (accept_3_2 103
  107 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 102 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 101 107 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 230 (accept_3_2 100 107 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 230 (Polychromatic418967fa.accept_13_7_3_9_1_1142
  98 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 107 230 (accept_3_2 97
  107 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 107 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 96 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 107 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 95 107 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 230 (accept_3_2 94 107 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 92
  107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 107 230 (accept_3_2 91
  107 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 107 230
  (Polychromatic418967fa.accept_13_12_3_9_1_4341 90 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 89 107 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 230 (accept_3_2 88 107 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 107 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 230 (Polychromatic418967fa.accept_11_9_8_10_1_934
  86 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 107 230 (accept_3_2 85
  107 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 107 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 84 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 107 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 83 107 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 230 (accept_3_2 82 107 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 80
  107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 107 230 (accept_3_2 79
  107 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 107 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 78 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 107 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 230 (accept_3_2 76 107 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 107 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 230 (Polychromatic418967fa.accept_7_4_2_6_1_337
  74 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 107 230 (accept_3_2 73
  107 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 107 230
  (Polychromatic418967fa.accept_13_7_3_9_1_1142 72 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 107 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 107 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 230 (accept_3_2 70 107 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 230
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 230 (accept_3_2 67 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 230 (accept_3_2 64 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 107 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 230
  (Polychromatic418967fa.accept_25_12_7_5_1_13742 62 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 107 230 (accept_3_2 61 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 107 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 107 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 107 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 230 (accept_3_2 58 107 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57
  107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 230 (accept_3_2 55 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 230 (Polychromatic418967fa.accept_13_2_3_9_1_2610 54 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 230 (accept_3_2 52 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 107 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 230 (accept_3_2 49 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 230 (accept_3_2 46 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 107 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 230
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 230 (accept_3_2 43 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 230 (accept_3_2 40 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 230 (accept_3_2 37 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 230 (Polychromatic418967fa.accept_16_3_11_6_1_4467 35 107 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 230 (accept_3_2 34 107 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 107 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 230 (accept_3_2 31 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 230 (accept_3_2 28 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 230
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 26 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 230 (accept_3_2 25 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 230 (Polychromatic418967fa.accept_19_4_12_2_1_11158 23 107 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 230 (accept_3_2 22 107 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 107 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 230 (accept_3_2 19 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 230 (accept_3_2 16 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 230
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 14 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 230 (accept_3_2 13 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 230 (accept_3_2 10 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 107 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 230 (accept_3_2 7 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 230 (accept_3_2 4 107 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 230 (accept_3_2 1 107 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 230 (allA_of_3_0 106 106 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 230
  (allA_succ_of_accept 104 105 230 (Polychromatic418967fa.accept_11_5_6_10_1_1432 104 105 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 230 (accept_3_2 103 105 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 102 105 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 105 230 5 20 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 105 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 105 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 105 230 (Polychromatic418967fa.accept_9_8_6_5_1_513
  98 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 230 (accept_3_2 97
  105 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 230
  (Polychromatic418967fa.accept_13_5_1_9_1_618 96 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 95 105 230 5 19 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 94 105 230 (accept_3_2 94 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 105 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 93 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 92 105 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 230 (accept_3_2 91 105 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 105 230 5 18 21 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 105 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 230 (accept_3_2 88 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 230 (Polychromatic418967fa.accept_13_8_1_9_1_1178 86 105 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 105 230 5 17 21 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 105 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 84 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 105 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 105 230 (accept_3_2 82 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 105 230 (Polychromatic418967fa.accept_19_5_10_2_1_1731 81 105 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 105 230 5 16 21 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 105 230 (accept_3_2 79 105 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 230 (Polychromatic418967fa.accept_12_6_9_2_1_311
  78 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 230 (accept_3_2 76 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75
  105 230 5 15 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 105 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 74 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 230 (accept_3_2 73 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 105 230 (Polychromatic418967fa.accept_20_12_5_10_1_9540 72 105 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 105 230 5 14 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 105 230 (Polychromatic418967fa.accept_14_13_7_6_1_3525 69 105 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 230
  (Polychromatic418967fa.accept_19_11_10_2_1_9757 68 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 105 230 (accept_3_2 67 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 105 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 105 230 5 13 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 105 230 (accept_3_2 64 105 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 105 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 105 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 105 230 (accept_3_2 61 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60
  105 230 5 12 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 105 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 230 (accept_3_2 58 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 105 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 105 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 230 (Polychromatic418967fa.accept_9_2_6_5_1_227
  56 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 105 230 5 11 21 46
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 105 230
  (Polychromatic418967fa.accept_12_6_9_2_1_311 54 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 230 (accept_3_2 52 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 105 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 105 230 5 10 21 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 105 230 (accept_3_2 49 105 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 105 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 230 (accept_3_2 46 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  105 230 5 9 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 105 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 105 230 (accept_3_2 43 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 105 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 105 230 5 8 21 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 105 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 105 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 230 (accept_3_2 37 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 105 230 (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 105 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 105 230 5 7 21 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 230 (accept_3_2 34 105 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 230
  (Polychromatic418967fa.accept_20_13_5_10_1_3590 33 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 105 230 (Polychromatic418967fa.accept_13_6_1_9_1_619 32 105 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 230 (accept_3_2 31 105 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 230 5 6 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 29
  105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 230 (accept_3_2 28
  105 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 105 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 105 230 5 5 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 105 230 (Polychromatic418967fa.accept_13_11_1_9_1_1179
  24 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 230 (accept_3_2 22 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 105 230 5 4 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 105 230 (accept_3_2 19 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 105 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 230 (accept_3_2 16 105 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 230 5 3 21 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 230
  (Polychromatic418967fa.accept_20_14_5_10_1_3647 14 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 105 230 (accept_3_2 13 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 105 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 105 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 105 230 5 2 21 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 105 230
  (Polychromatic418967fa.accept_20_9_5_10_1_12356 9 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 230 (accept_3_2 7 105 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 105 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 105 230 5 1 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 230 (accept_3_2 4 105 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 105 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 230
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 230 (accept_3_2 1 105 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 230 (allA_succ_of_accept 103 104 230 (accept_3_2 103 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 104 230 2 51 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 104 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 101 104 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 104 230 2 50 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 104 230
  (Polychromatic418967fa.accept_15_9_14_5_1_2086 99 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 104 230 2 49 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 104 230 (accept_3_2 97 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 104 230 2 48 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 104 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 95 104 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 104 230 2 47 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 104 230
  (Polychromatic418967fa.accept_19_17_9_2_1_12492 93 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 104 230 2 46 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 104 230 (accept_3_2 91 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 104 230 2 45 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 104 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 89 104 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 104 230 2 44 52 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 104 230
  (Polychromatic418967fa.accept_19_11_9_2_1_1729 87 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 104 230 2 43 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 104 230 (accept_3_2 85 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 104 230 2 42 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 104 230 (Polychromatic418967fa.accept_11_6_5_10_1_2724 83 104 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 104 230 2 41 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 104 230
  (Polychromatic418967fa.accept_11_4_5_10_1_926 81 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 104 230 2 40 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 104 230 (accept_3_2 79 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 104 230 2 39 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 104 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 104 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 230 2 38 52 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 230
  (Polychromatic418967fa.accept_17_7_2_9_1_6396 75 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 104 230 2 37 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 104 230 (accept_3_2 73 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 104 230 2 36 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 104 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 71 104 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 230 2 35 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 230
  (Polychromatic418967fa.accept_15_9_14_5_1_2086 69 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 104 230 2 34 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 104 230 (accept_3_2 67 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 104 230 2 33 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 104 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 65 104 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 104 230 2 32 52 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 104 230
  (Polychromatic418967fa.accept_27_9_23_14_1_2233 63 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 104 230 2 31 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 104 230 (accept_3_2 61 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 104 230 2 30 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 104 230 (Polychromatic418967fa.accept_11_4_5_10_1_926 59 104 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 230 2 29 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 230
  (Polychromatic418967fa.accept_24_9_8_14_1_10466 57 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 104 230 2 28 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 104 230 (accept_3_2 55 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 230 2 27 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 104 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 230 2 26 52 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 230
  (Polychromatic418967fa.accept_15_6_14_5_1_2976 51 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 230 2 25 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 230 (accept_3_2 49 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 230 2 24 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 104 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 104 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 230 2 23 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 230
  (Polychromatic418967fa.accept_17_11_2_9_1_6358 45 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 104 230 2 22 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 104 230 (accept_3_2 43 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 230 2 21 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 104 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 230 2 20 52 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 230
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 39 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 230 2 19 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 230 (accept_3_2 37 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 230 2 18 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 104 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 104 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 230 2 17 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 230
  (Polychromatic418967fa.accept_24_9_8_14_1_10466 33 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 104 230 2 16 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 104 230 (accept_3_2 31 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 104 230 2 15 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 104 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 104 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 230 2 14 52 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 230
  (Polychromatic418967fa.accept_22_5_16_10_1_7349 27 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 104 230 2 13 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 104 230 (accept_3_2 25 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 230 2 12 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 104 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 104 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 230 2 11 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 230
  (Polychromatic418967fa.accept_15_6_14_5_1_2976 21 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 230 2 10 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 104 230 (accept_3_2 19 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 104 230 2 9 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 104 230 (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 104 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 230 2 8 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 230
  (Polychromatic418967fa.accept_11_4_5_10_1_926 15 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 104 230 2 7 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 104 230 (accept_3_2 13 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 104 230 2 6 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 104 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 104 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 104 230 2 5 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 104 230
  (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 104 230 2 4 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 104 230 (accept_3_2 7 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104
  230 2 3 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  104 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 104 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 104 230 2 2 52 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 104 230 (Polychromatic418967fa.accept_22_3_16_10_1_7310 3 104 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 230 2 1 52 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 230 (accept_3_2 1 104 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 230 (allA_of_3_0 103 103 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 230 (allA_succ_of_accept 101
  102 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 101 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 102 230 2 50 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 102 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 99 102 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 102 230 2 49 51 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 230 (accept_3_2 97 102 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 102 230 2 48 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 102 230
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 95 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 102 230 2 47 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 102 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 93 102 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 102 230 2 46 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 230 (accept_3_2 91 102 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 102 230 2 45 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 102 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 89
  102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 102 230 2 44 51 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 102 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 87 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 102 230 2 43 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 102 230 (accept_3_2 85 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 230 2 42 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 83 102 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 102 230 2 41 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 102 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 81 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 102 230 2 40 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 102 230 (accept_3_2 79 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 230 2 39 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 230 (Polychromatic418967fa.accept_15_2_12_5_1_2107 77 102 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 230 2 38 51 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 102 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 102 230 2 37 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 102 230 (accept_3_2 73 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 230 2 36 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 102 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 230 2 35 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 102 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 69 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 102 230 2 34 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 102 230 (accept_3_2 67 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 230 2 33 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 65 102 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 230 2 32 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 102 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 102 230 2 31 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 102 230 (accept_3_2 61 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 230 2 30 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 102 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 230 2 29 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 102 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 102 230 2 28 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 102 230 (accept_3_2 55 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 230 2 27 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 102 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 230 2 26 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 102 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 102 230 2 25 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 102 230 (accept_3_2 49 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 230 2 24 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 102 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 230 2 23 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 102 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 102 230 2 22 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 102 230 (accept_3_2 43 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 230 2 21 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 230 (Polychromatic418967fa.accept_13_2_11_9_1_591 41 102 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 230 2 20 51 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 230 2 19 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 230 (accept_3_2 37 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 230 2 18 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 102 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 230 2 17 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 102 230 2 16 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 102 230 (accept_3_2 31 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 230 2 15 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 102 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 230 2 14 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 230 2 13 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 230 (accept_3_2 25 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 230 2 12 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 102 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 230 2 11 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 230 2 10 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 230 (accept_3_2 19 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 230 2 9 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 102 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 102 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 230 2 8 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 102 230 2 7 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 102 230 (accept_3_2 13 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 230 2 6 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 102 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 102 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 230 2 5 51 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 230 2 4 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 230 (accept_3_2 7 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102
  230 2 3 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  102 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 102 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 230 2 2 51 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 102 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 102 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 230 2 1 51 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 230 (accept_3_2 1 102 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 230 (allA_succ_of_accept 100 101 230 (accept_3_2 100 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 101 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 98 101 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 230 (accept_3_2 97 101 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 230 (Polychromatic418967fa.accept_9_6_2_5_1_506
  96 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 101 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 101 230 (accept_3_2 94 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 101 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 101 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 92 101 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 230 (accept_3_2 91 101 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 230 (Polychromatic418967fa.accept_13_12_10_9_1_1166 90 101
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 89 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 101 230 (accept_3_2 88 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 101 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 101 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 86 101 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 230 (accept_3_2 85 101 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 101 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 101 230 (accept_3_2 82 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 101 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 101 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 101 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 230 (accept_3_2 79 101 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 101 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 230
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 77 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 101 230 (accept_3_2 76 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 101 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 101 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 74 101 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 230 (accept_3_2 73 101 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 72
  101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 230 (accept_3_2 70 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 68 101 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 230 (accept_3_2 67 101 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 101 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 65 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 230 (accept_3_2 64 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 101 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 230 (accept_3_2 61 101 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 101 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 230 (accept_3_2 58 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 230 (Polychromatic418967fa.accept_11_1_2_10_1_1426 56 101 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 230 (accept_3_2 55 101 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 230 (Polychromatic418967fa.accept_15_9_11_5_1_1283 54 101
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 53 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 230 (accept_3_2 52 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 230 (Polychromatic418967fa.accept_19_12_6_2_1_5424 50 101 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 230 (accept_3_2 49 101 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 101 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 101 230 (accept_3_2 46 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 101 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 101 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 101 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 230 (accept_3_2 43 101 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 101 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 230
  (Polychromatic418967fa.accept_18_5_11_14_1_7203 41 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 101 230 (accept_3_2 40 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 101 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 101 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 230 (Polychromatic418967fa.accept_13_12_10_9_1_1166 38 101
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 230 (accept_3_2 37 101
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 230
  (Polychromatic418967fa.accept_15_6_11_5_1_168 36 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 101 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 101 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 230 (accept_3_2 34 101 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 101 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 230 (Polychromatic418967fa.accept_7_4_3_6_1_340
  32 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 230 (accept_3_2 31
  101 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 101 230 (Polychromatic418967fa.accept_19_10_6_2_1_6907 29 101 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 230 (accept_3_2 28 101 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 101 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 101 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 230 (Polychromatic418967fa.accept_9_8_2_5_1_237
  26 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 230 (accept_3_2 25
  101 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 24 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 101 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 101 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 230 (accept_3_2 22 101 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 101 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 230 (Polychromatic418967fa.accept_12_8_5_2_1_746
  20 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 230 (accept_3_2 19
  101 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 101 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 101 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 230 (accept_3_2 16 101 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 101 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 101 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 230 (Polychromatic418967fa.accept_13_1_10_9_1_215
  14 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 230 (accept_3_2 13
  101 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 12 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 101 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 101 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 230 (accept_3_2 10 101 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 101 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 8
  101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 230 (accept_3_2 7 101
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 6 101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 101 230 (Polychromatic418967fa.accept_18_5_11_14_1_7203 5 101 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 230 (accept_3_2 4 101 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 101 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 101 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 2
  101 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 230 (accept_3_2 1 101
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 230 (allA_of_3_0 100 100 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 230 (allA_succ_of_accept 98 99
  230 (Polychromatic418967fa.accept_13_7_8_9_1_1158 98 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 99 230 (accept_3_2 97 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 99 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 96 99 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 99 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 230 (accept_3_2 94 99 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 93
  99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 230
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 92 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 230 (accept_3_2 91 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 90 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 89 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 230 (accept_3_2 88 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 230 (Polychromatic418967fa.accept_15_12_9_5_1_2973 87 99 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 86 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 230 (accept_3_2 85 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 230 (Polychromatic418967fa.accept_16_4_3_6_1_6805 84 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 230 (accept_3_2 82 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 99 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 230
  (Polychromatic418967fa.accept_17_12_14_9_1_5079 80 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 230 (accept_3_2 79 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 78 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 230 (accept_3_2 76 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 99 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 230
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 74 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 230 (accept_3_2 73 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 230 (accept_3_2 70 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 99 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 68 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 230 (accept_3_2 67 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 66 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 230 (accept_3_2 64 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 230 (Polychromatic418967fa.accept_13_11_8_9_1_1161 63 99 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 230
  (Polychromatic418967fa.accept_19_5_4_2_1_6840 62 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 230 (accept_3_2 61 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 230 (Polychromatic418967fa.accept_18_6_9_14_1_9915 60 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 230 (accept_3_2 58 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 99 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 230
  (Polychromatic418967fa.accept_13_4_8_9_1_1156 56 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 230 (accept_3_2 55 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 230 (accept_3_2 52 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 99 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 230
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 50 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 230 (accept_3_2 49 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 230 (Polychromatic418967fa.accept_15_3_9_5_1_2082 48 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 230 (accept_3_2 46 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 99 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 230 (accept_3_2 43 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 230 (accept_3_2 40 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 230 (Polychromatic418967fa.accept_17_5_14_9_1_5104 39 99 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 230
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 38 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 230 (accept_3_2 37 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 230 (Polychromatic418967fa.accept_16_4_3_6_1_6805 36 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 230 (accept_3_2 34 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 99 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 230
  (Polychromatic418967fa.accept_25_7_24_5_1_13741 32 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 230 (accept_3_2 31 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 230 (accept_3_2 28 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 230 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 99 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 230 (accept_3_2 25 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 230 (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 230 (accept_3_2 22 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 99 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 230
  (Polychromatic418967fa.accept_13_7_8_9_1_1158 20 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 230 (accept_3_2 19 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 230 (accept_3_2 16 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 230 (Polychromatic418967fa.accept_20_15_19_10_1_11039 15 99 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 230
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 14 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 230 (accept_3_2 13 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 230 (accept_3_2 10 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 230
  (Polychromatic418967fa.accept_22_8_11_10_1_5822 8 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 230 (accept_3_2 7 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  230 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 99 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 230 (accept_3_2 4 99 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 230 (Polychromatic418967fa.accept_13_3_8_9_1_1134 3 99 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  99 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 230 (accept_3_2 1 99 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  230 (allA_succ_of_accept 97 98 230 (accept_3_2 97 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96
  98 230 2 48 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 98 230 (Polychromatic418967fa.accept_13_4_7_9_1_5260 95 98 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 98 230 2 47 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 98 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 93
  98 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 98 230 2 46 49 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 98 230 (accept_3_2 91
  98 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 98 230 2 45 49 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 98 230
  (Polychromatic418967fa.accept_13_11_7_9_1_612 89 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 98 230 2 44 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 98 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 87 98 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 98 230 2 43 49 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 98 230 (accept_3_2 85 98 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98 230 2 42 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 98 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 83
  98 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 98 230 2 41 49 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 98 230
  (Polychromatic418967fa.accept_13_3_7_9_1_1153 81 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 98 230 2 40 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 98 230 (accept_3_2 79 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 98 230 2 39 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 98 230 (Polychromatic418967fa.accept_18_5_8_14_1_1282 77 98 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 98 230 2 38 49 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 98 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 75 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 98 230 2 37 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 98 230 (accept_3_2 73 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 98 230 2 36 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 98 230 (Polychromatic418967fa.accept_13_6_7_9_1_1848 71 98 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 98 230 2 35 49 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 98 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 69 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 98 230 2 34 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 98 230 (accept_3_2 67 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 98 230 2 33 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 98 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 98 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 98 230 2 32 49 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 98 230
  (Polychromatic418967fa.accept_13_11_7_9_1_612 63 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 98 230 2 31 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 98 230 (accept_3_2 61 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 98 230 2 30 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 98 230 (Polychromatic418967fa.accept_15_14_8_5_1_2104 59 98 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 98 230 2 29 49 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 98 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 98 230 2 28 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 98 230 (accept_3_2 55 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 98 230 2 27 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 98 230 (Polychromatic418967fa.accept_21_11_14_20_1_12235 53 98 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 98 230 2 26 49 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 98 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 98 230 2 25 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 98 230 (accept_3_2 49 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 98 230 2 24 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 98 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 98 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 230 2 23 49 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 230
  (Polychromatic418967fa.accept_13_6_7_9_1_1848 45 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 98 230 2 22 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 98 230 (accept_3_2 43 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 98 230 2 21 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 98 230 (Polychromatic418967fa.accept_13_2_7_9_1_2616 41 98 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 98 230 2 20 49 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 98 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 98 230 2 19 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 98 230 (accept_3_2 37 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 98 230 2 18 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 98 230 (Polychromatic418967fa.accept_16_3_2_6_1_4461 35 98 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 98 230 2 17 49 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 98 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 98 230 2 16 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 98 230 (accept_3_2 31 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 98 230 2 15 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 98 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 98 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 230 2 14 49 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 230
  (Polychromatic418967fa.accept_15_12_8_5_1_5048 27 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 230 2 13 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 98 230 (accept_3_2 25 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 98 230 2 12 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 98 230 (Polychromatic418967fa.accept_18_5_8_14_1_1282 23 98 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 98 230 2 11 49 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 98 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 98 230 2 10 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 98 230 (accept_3_2 19 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 98 230 2 9 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 98 230 (Polychromatic418967fa.accept_13_4_7_9_1_5260 17 98 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 230 2 8 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 15
  98 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 230 2 7 49 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 230 (accept_3_2 13
  98 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98 230 2 6 49 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 98 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 98 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 98 230 2 5 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 98 230 (Polychromatic418967fa.accept_16_9_2_6_1_4434 9 98 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 230 2 4 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 230 (accept_3_2 7 98 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 98 230 2 3 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 98 230 (Polychromatic418967fa.accept_17_5_13_9_1_9018 5 98 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 230 2 2 49 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 98
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 230 2 1 49 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 230 (accept_3_2 1 98
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  230 (allA_of_3_0 97 97 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 230 (allA_succ_of_accept 95 96 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 95 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 96 230 2 47 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 96 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 93 96 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 96 230 2 46 48 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 96 230 (accept_3_2 91 96 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 230 2 45 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 89
  96 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 230 2 44 48 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 230
  (Polychromatic418967fa.accept_15_12_6_5_1_1275 87 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 96 230 2 43 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 96 230 (accept_3_2 85 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 96 230 2 42 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 96 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 83 96 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 230 2 41 48 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 81 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 96 230 2 40 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 96 230 (accept_3_2 79 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 96 230 2 39 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 96 230 (Polychromatic418967fa.accept_22_11_8_10_1_13740 77 96 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 96 230 2 38 48 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 96 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 75 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 96 230 2 37 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 96 230 (accept_3_2 73 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 96 230 2 36 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 96 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 96 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 230 2 35 48 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 96 230
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 69 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 96 230 2 34 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 96 230 (accept_3_2 67 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 96 230 2 33 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 96 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 96 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 96 230 2 32 48 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 96 230
  (Polychromatic418967fa.accept_15_3_6_5_1_2079 63 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 96 230 2 31 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 96 230 (accept_3_2 61 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 230 2 30 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 96 230 (Polychromatic418967fa.accept_15_14_6_5_1_7215 59 96 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96 230 2 29 48 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 96 230
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 96 230 2 28 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 96 230 (accept_3_2 55 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 96 230 2 27 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 96 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 96 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 230 2 26 48 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 96 230
  (Polychromatic418967fa.accept_19_13_1_2_1_11154 51 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 96 230 2 25 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 96 230 (accept_3_2 49 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 230 2 24 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 96 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 96 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 230 2 23 48 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 230
  (Polychromatic418967fa.accept_18_9_6_14_1_5913 45 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 96 230 2 22 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 96 230 (accept_3_2 43 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 230 2 21 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 96 230 (Polychromatic418967fa.accept_13_2_5_9_1_610 41 96 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96 230 2 20 48 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 96 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 96 230 2 19 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 96 230 (accept_3_2 37 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 96 230 2 18 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 96 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 96 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 230 2 17 48 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 230
  (Polychromatic418967fa.accept_15_3_6_5_1_2079 33 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 96 230 2 16 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 96 230 (accept_3_2 31 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 230 2 15 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 96 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 96 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 230 2 14 48 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 230
  (Polychromatic418967fa.accept_13_1_5_9_1_226 27 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 96 230 2 13 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 96 230 (accept_3_2 25 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 230 2 12 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 96 230 (Polychromatic418967fa.accept_25_23_21_5_1_13739 23 96 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 230 2 11 48 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 96 230 2 10 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 96 230 (accept_3_2 19 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 96 230 2 9 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 96 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 96 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 230 2 8 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 15
  96 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 230 2 7 48 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 230 (accept_3_2 13
  96 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 230 2 6 48 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 96 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 96 230 2 5 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 96 230 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 96 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 96 230 2 4 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 230 (accept_3_2 7 96 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 96 230 2 3 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 96 230 (Polychromatic418967fa.accept_20_5_16_10_1_3558 5 96 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 230 2 2 48 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 96 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 96
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 230 2 1 48 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 230 (accept_3_2 1 96
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 230
  (allA_succ_of_accept 94 95 230 (accept_3_2 94 95 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 92 95 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 230 (accept_3_2 91 95 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 95 230 5 18 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 95 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 89 95
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 95 230 (accept_3_2 88 95 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 95 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 87
  95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 95 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 86 95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 95 230 5 17 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 95 230 (Polychromatic418967fa.accept_13_6_4_9_1_4326 84 95 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 230 (Polychromatic418967fa.accept_13_5_4_9_1_601 83 95 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 95 230 (accept_3_2 82 95 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 95 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 81
  95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 95 230 5 16 19 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 95 230 (accept_3_2 79
  95 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 230
  (Polychromatic418967fa.accept_20_18_15_10_1_12414 78 95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 95 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 95 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 95 230 (accept_3_2 76 95 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 75 95 230 5 15 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 95 230 (Polychromatic418967fa.accept_20_14_15_10_1_3554 74 95
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 230 (accept_3_2 73 95 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 72
  95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 230
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 71 95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 95 230 5 14 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 95 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 95 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 95 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 68 95 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 230 (accept_3_2 67 95 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 66
  95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 95 230 5 13 19 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 95 230 (accept_3_2 64
  95 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 95 230
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 95 230 (Polychromatic418967fa.accept_18_8_5_14_1_3353 62 95 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 230 (accept_3_2 61 95 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 95 230 5 12 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 95 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 95 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 95 230 (accept_3_2 58 95 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 95 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 95 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 95 230
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 95 230 5 11 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 95 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 95 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 95 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 230 (accept_3_2 52 95 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 95 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 51
  95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 95 230 5 10 19 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 95 230 (accept_3_2 49
  95 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 230
  (Polychromatic418967fa.accept_20_8_15_10_1_8045 48 95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 95 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 95 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 230 (accept_3_2 46 95 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 95 230 5 9 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 95 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 95 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 230 (accept_3_2 43 95 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 230 (Polychromatic418967fa.accept_20_2_15_10_1_5036 42 95 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 95 230 5 8 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 95 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 95 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 230 (accept_3_2 37 95 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 230 (Polychromatic418967fa.accept_11_3_7_10_1_180
  36 95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 95 230 5 7 19 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 95 230 (accept_3_2 34
  95 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 95 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 95 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 230 (accept_3_2 31 95 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 95 230 5 6 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 95 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 95 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 230 (accept_3_2 28 95 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 95 230 5 5 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 95 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 95 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 95 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 230 (accept_3_2 22 95 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 95 230 5 4 19 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 95 230 (accept_3_2 19
  95 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 230
  (Polychromatic418967fa.accept_13_5_4_9_1_601 18 95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 95 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 95 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 230 (accept_3_2 16 95 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 95 230 5 3 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 95 230 (Polychromatic418967fa.accept_11_3_7_10_1_180 14 95 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 230 (accept_3_2 13 95 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 95 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 230
  (Polychromatic418967fa.accept_18_11_5_14_1_4560 11 95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 95 230 5 2 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 95 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 95 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 95 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 230 (accept_3_2 7 95 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 230 (Polychromatic418967fa.accept_13_6_4_9_1_4326 6
  95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 95 230 5 1 19 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 95 230 (accept_3_2 4 95
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 230 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 95 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 230 (accept_3_2 1 95 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 230
  (allA_of_3_0 94 94 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 230 (allA_succ_of_accept 92 93 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 92 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 230 (accept_3_2 91 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 90 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 230 (accept_3_2 88 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 93 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 230
  (Polychromatic418967fa.accept_17_1_8_9_1_1810 86 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 230 (accept_3_2 85 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 230 (Polychromatic418967fa.accept_13_6_2_9_1_1188 84 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 230 (accept_3_2 82 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 93 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 80 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 230 (accept_3_2 79 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 230 (accept_3_2 76 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 93 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 74 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 230 (accept_3_2 73 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 230 (Polychromatic418967fa.accept_11_6_5_10_1_2724 72 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 230 (accept_3_2 70 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 93 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 230
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 68 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 230 (accept_3_2 67 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 230 (accept_3_2 64 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 93 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 62 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 230 (accept_3_2 61 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 230 (accept_3_2 58 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 93 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 230 (accept_3_2 55 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 230 (accept_3_2 52 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 93 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 230 (accept_3_2 49 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 230 (Polychromatic418967fa.accept_11_4_5_10_1_926 48 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 230 (accept_3_2 46 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 93 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 230 (accept_3_2 43 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 230 (accept_3_2 40 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 93 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 230 (accept_3_2 37 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 230 (accept_3_2 34 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 93 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 230 (accept_3_2 31 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 230 (accept_3_2 28 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 93 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 230 (accept_3_2 25 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 230 (accept_3_2 22 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 230 (Polychromatic418967fa.accept_15_6_3_5_1_607 21 93 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 230 (accept_3_2 19 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 230 (accept_3_2 16 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 93 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 230
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 14 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 230 (accept_3_2 13 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 230 (Polychromatic418967fa.accept_18_12_3_14_1_5919 12 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 230 (accept_3_2 10 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 230 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 93 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 230 (accept_3_2 7 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  230 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 93 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 230 (accept_3_2 4 93 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 93
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 230 (accept_3_2 1 93 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 230
  (allA_succ_of_accept 91 92 230 (accept_3_2 91 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 92
  230 2 45 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  89 92 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 92 230 2 44 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 92 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 87 92 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 92 230 2 43 46 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 92 230 (accept_3_2 85 92 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 92 230 2 42 46 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 92 230
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 83 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 92 230 2 41 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 92 230 (Polychromatic418967fa.accept_19_5_16_2_1_1717 81 92 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 92 230 2 40 46 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 92 230 (accept_3_2 79 92 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 92 230 2 39 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 92 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 77
  92 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 92 230 2 38 46 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 92 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 75 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 92 230 2 37 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 92 230 (accept_3_2 73 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 92 230 2 36 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 92 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 92 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 92 230 2 35 46 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 92 230 23 3 4 10 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 92 230 2 34 46 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 92 230 (accept_3_2 67 92 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 92 230 2 33 46 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 92 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 92 230 2 32 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 92 230 (Polychromatic418967fa.accept_13_11_1_9_1_1179 63 92 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 92 230 2 31 46 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 92 230 (accept_3_2 61 92 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92 230 2 30 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274
  59 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 92 230 2 29 46 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 92 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 57 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 92 230 2 28 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 92 230 (accept_3_2 55 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 92 230 2 27 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 92 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 92 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 92 230 2 26 46 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 92 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 92 230 2 25 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 92 230 (accept_3_2 49 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 92 230 2 24 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 92 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 92 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 92 230 46 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 92 230 (Polychromatic418967fa.accept_13_6_1_9_1_619 45
  92 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 230 2 22 46 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 230 (accept_3_2 43
  92 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 230 2 21 46 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 230
  (Polychromatic418967fa.accept_12_5_8_2_1_309 41 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 92 230 2 20 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 92 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 92 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 92 230 2 19 46 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 92 230 (accept_3_2 37 92 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92 230 2 18 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 92 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 35
  92 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 230 2 17 46 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 92 230 2 16 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 92 230 (accept_3_2 31 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 92 230 2 15 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 92 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 92 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 92 230 2 14 46 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 92 230
  (Polychromatic418967fa.accept_11_5_4_10_1_524 27 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 92 230 2 13 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 92 230 (accept_3_2 25 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 92 230 2 12 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 23 92 230 23 1 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 22 92 230 2 11 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 92 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 92 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 92 230 2 10 46 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 92 230 (accept_3_2 19 92 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92 230 2 9 46 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 92 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 92 230 2 8 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 92 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 92 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 230 2 7 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 230 (accept_3_2 13 92 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 230 2 6 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 92 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 92 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 230 2 5 46 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 92 230 2 4 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 92 230 (accept_3_2 7 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 230
  2 3 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92
  230 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 92 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 92 230 2 2 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 92 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 92 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 230 2 1 46 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 230 (accept_3_2 1 92 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 230
  (allA_of_3_0 91 91 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 230 (allA_succ_of_accept 89 90 230
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 89 90 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 90 230 2 44 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 90 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 87 90 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 90 230 2 43 45 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 85 90 230 5 17 18 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 90 230 2 42 45 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 230
  (Polychromatic418967fa.accept_19_7_14_2_1_4095 83 90 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 90 230 2 41 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 90 230 (Polychromatic418967fa.accept_12_9_6_2_1_1273 81 90 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 90 230 10 8 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 230 (accept_3_2 79 90 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 230 2 39 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 230 (Polychromatic418967fa.accept_19_1_14_2_1_4134 77 90 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 230 2 38 45 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 90 230 5 15 18 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 90 230 2 37 45 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 90 230
  (accept_3_2 73 90 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 230 2 36 45 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 230
  (Polychromatic418967fa.accept_22_5_2_10_1_10683 71 90 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 90 230 10 7 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 90 230 (Polychromatic418967fa.accept_12_9_6_2_1_1273 69 90 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 90 230 2 34 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 90 230 (accept_3_2 67 90 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 230 2 33 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 90 230 5 13 18 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 90 230 2 32 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 63
  90 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 90 230 2 31 45 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 90 230 (accept_3_2 61
  90 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 230 10 6 9 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 230
  (Polychromatic418967fa.accept_25_9_15_5_1_13738 59 90 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 90 230 2 29 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 90 230 (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 90 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 90 230 2 28 45 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 90 230 5 11 18 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 90 230 2 27 45 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 230
  (Polychromatic418967fa.accept_21_11_6_20_1_4589 53 90 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 90 230 2 26 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 90 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 51 90 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 90 230 10 5 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 230 (accept_3_2 49 90 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 230 2 24 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 230 (Polychromatic418967fa.accept_13_8_12_9_1_1168 47 90 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 230 2 23 45 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 90 230 5 9 18 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 90 230 2 22 45 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 230
  (accept_3_2 43 90 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 230 2 21 45 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 230
  (Polychromatic418967fa.accept_17_7_5_9_1_7763 41 90 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 90 230 10 4 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 90 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 39 90 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 230 2 19 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 230 (accept_3_2 37 90 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 230 2 18 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 90 230 5 7 18 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 90 230 2 17 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 230 (Polychromatic418967fa.accept_12_9_6_2_1_1273
  33 90 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 90 230 2 16 45 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 230
  (accept_3_2 31 90 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 230 10 3 9 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 230
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 29 90 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 90 230 2 14 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 90 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 90 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 230 2 13 45 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 90 230 5 5 18 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 90 230 2 12 45 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 230
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 90 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 90 230 2 11 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 90 230 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 90 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 230 10 2 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 230 (accept_3_2 19 90 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 230 2 9 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 230 (Polychromatic418967fa.accept_19_17_14_2_1_4116 17 90
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 230 2 8 45 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 230 5 3 18 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 230 2 7 45 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 230 (accept_3_2 13
  90 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 230 2 6 45 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 230
  (Polychromatic418967fa.accept_21_11_6_20_1_4589 11 90 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 90 230 10 1 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 90 230 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 90 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 230 2 4 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 230 (accept_3_2 7 90 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 90 230 2 3 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 5 90 230 5 1 18 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 4 90 230 2 2 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 90 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 90 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 230 2 1 45 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 230 (accept_3_2 1 90 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 90
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 230
  (allA_succ_of_accept 88 89 230 (accept_3_2 88 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 230 (Polychromatic418967fa.accept_11_9_1_10_1_920 86 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 230 (accept_3_2 85 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 89 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 230 (accept_3_2 82 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 80 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 230 (accept_3_2 79 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 89 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 230
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 77 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 230 (accept_3_2 76 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 74 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 230 (accept_3_2 73 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 230 (Polychromatic418967fa.accept_13_7_11_9_1_1858 72 89 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 230 (accept_3_2 70 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 230 (Polychromatic418967fa.accept_11_2_1_10_1_196 68 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 230 (accept_3_2 67 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 89 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 230 (accept_3_2 64 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 230 (Polychromatic418967fa.accept_15_2_14_5_1_2072 62 89 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 230 (accept_3_2 61 89 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 89 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 230 (accept_3_2 58 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 230 (accept_3_2 55 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 230 (Polychromatic418967fa.accept_13_2_11_9_1_591 54 89 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 230 (accept_3_2 52 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 230 (accept_3_2 49 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 89 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 230 (accept_3_2 46 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 230 (accept_3_2 43 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 89 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 230
  (Polychromatic418967fa.accept_13_2_11_9_1_591 41 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 230 (accept_3_2 40 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 230 (accept_3_2 37 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 89 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 230 (accept_3_2 34 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 230 (accept_3_2 31 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 89 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 230
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 230 (accept_3_2 28 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 230 (Polychromatic418967fa.accept_19_7_13_2_1_2878 26 89 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 230 (accept_3_2 25 89 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 89 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 230 (accept_3_2 22 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 230 (accept_3_2 19 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 89 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 230
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 230 (accept_3_2 16 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 230 (Polychromatic418967fa.accept_13_1_11_9_1_1857 14 89 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 230 (accept_3_2 13 89 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 89 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 230 (accept_3_2 10 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 230 (accept_3_2 7 89 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 89 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 230
  (Polychromatic418967fa.accept_20_5_9_10_1_12409 5 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 230 (accept_3_2 4 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 89 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 89 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 230 (accept_3_2 1 89 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 230 (allA_of_3_0 88 88 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 230
  (allA_succ_of_accept 86 87 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 86 87 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 230 (accept_3_2 85 87 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 83
  87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 230 (accept_3_2 82 87
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 230 (Polychromatic418967fa.accept_4_1_3_2_1_3
  81 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 87 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 80 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 87 230 (accept_3_2 79 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  87 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 78 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 87 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 230 (accept_3_2 76 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 87 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 74 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 230 (accept_3_2 73 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  87 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 87 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 230 (accept_3_2 70 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 87 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 230
  (Polychromatic418967fa.accept_15_8_12_5_1_2987 68 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 230 (accept_3_2 67 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 230 (accept_3_2 64 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 230 (Polychromatic418967fa.accept_16_15_7_6_1_1453 63 87 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 230 (accept_3_2 61 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 230 (accept_3_2 58 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 87 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 230
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 230 (accept_3_2 55 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 230 (accept_3_2 52 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 87 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 230
  (Polychromatic418967fa.accept_22_6_21_10_1_12180 50 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 87 230 (accept_3_2 49 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 87 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 87 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 230 (accept_3_2 46 87 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 230 (accept_3_2 43 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 230 (accept_3_2 40 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 87 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 230
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 230 (accept_3_2 37 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 230 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 230 (accept_3_2 34 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 87 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 230 (accept_3_2 31 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 230 (accept_3_2 28 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 230 (Polychromatic418967fa.accept_19_8_11_2_1_6876 27 87 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 230 (accept_3_2 25 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 230 (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 230 (accept_3_2 22 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 230
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 230 (accept_3_2 19 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 230 (accept_3_2 16 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 230 (Polychromatic418967fa.accept_16_15_7_6_1_1453 15 87 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 230
  (Polychromatic418967fa.accept_22_14_21_10_1_13737 14 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 87 230 (accept_3_2 13 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 87 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 87 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 230 (accept_3_2 10 87 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 230 (accept_3_2 7 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  230 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 87 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 87 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 230 (accept_3_2 4 87 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 87 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 87
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 230 (accept_3_2 1 87 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 230
  (allA_succ_of_accept 85 86 230 (accept_3_2 85 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 86
  230 2 42 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  83 86 230 (Polychromatic418967fa.accept_15_8_11_5_1_169 83 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 86 230 2 41 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 86 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 86 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 86 230 2 40 43 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 86 230 (accept_3_2 79 86 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86 230 2 39 43 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 86 230
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 77 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 86 230 2 38 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 86 230 (Polychromatic418967fa.accept_19_18_10_2_1_2850 75 86 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 230 2 37 43 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 230 (accept_3_2 73 86 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 230 2 36 43 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 86 230 2 35 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 86 230 (Polychromatic418967fa.accept_13_4_8_9_1_1156 69 86 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 86 230 2 34 43 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 86 230 (accept_3_2 67 86 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 86 230 2 33 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 86 230 (Polychromatic418967fa.accept_19_8_10_2_1_5414
  65 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 86 230 2 32 43 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 86 230
  (Polychromatic418967fa.accept_11_8_9_10_1_503 63 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 86 230 2 31 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 86 230 (accept_3_2 61 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 86 230 2 30 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 86 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 86 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 86 230 2 29 43 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 86 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 86 230 2 28 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 86 230 (accept_3_2 55 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 86 230 2 27 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 86 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 86 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 230 2 26 43 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 230
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 51 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 230 2 25 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 86 230 (accept_3_2 49 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 86 230 2 24 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 86 230 (Polychromatic418967fa.accept_15_2_11_5_1_1266 47 86 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 86 230 2 23 43 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 86 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 86 230 2 22 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 86 230 (accept_3_2 43 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 86 230 2 21 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 86 230 (Polychromatic418967fa.accept_11_8_9_10_1_503 41 86 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 230 2 20 43 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 86 230 2 19 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 86 230 (accept_3_2 37 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 86 230 2 18 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 86 230 (Polychromatic418967fa.accept_20_15_6_10_1_9569 35 86 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 230 2 17 43 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 230
  (Polychromatic418967fa.accept_13_7_8_9_1_1158 33 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 230 2 16 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 86 230 (accept_3_2 31 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 86 230 2 15 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 86 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 86 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 230 2 14 43 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 230
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 230 2 13 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 86 230 (accept_3_2 25 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 86 230 2 12 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 86 230 (Polychromatic418967fa.accept_11_1_9_10_1_184 23 86 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 86 230 2 11 43 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 230
  (Polychromatic418967fa.accept_15_6_11_5_1_168 21 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 86 230 2 10 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 86 230 (accept_3_2 19 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 86 230 2 9 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 86 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 86 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 230 2 8 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  86 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 230 2 7 43 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 230 (accept_3_2 13
  86 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86 230 2 6 43 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 86 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 86 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 86 230 2 5 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 86 230 (Polychromatic418967fa.accept_15_9_11_5_1_1283 9 86 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 230 2 4 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 230 (accept_3_2 7 86 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 86 230 2 3 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 86 230 (Polychromatic418967fa.accept_19_5_10_2_1_1731 5 86 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 230 2 2 43 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 86
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 230 2 1 43 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 230 (accept_3_2 1 86
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 230
  (allA_of_3_0 85 85 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 230 (allA_succ_of_accept 83 84 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 83 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 84 230 2 41 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 84 230 (Polychromatic418967fa.accept_13_3_6_9_1_1150 81 84 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 84 230 2 40 42 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 230 (accept_3_2 79 84 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 230 2 39 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 230 (Polychromatic418967fa.accept_16_13_4_6_1_2322
  77 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 230 2 38 42 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 230
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 75 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 230 2 37 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 84 230 (accept_3_2 73 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 84 230 2 36 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 84 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 84 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 230 2 35 42 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 69 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 84 230 2 34 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 84 230 (accept_3_2 67 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 230 2 33 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 84 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 84 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 84 230 2 32 42 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 84 230
  (Polychromatic418967fa.accept_15_3_9_5_1_2082 63 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 84 230 2 31 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 84 230 (accept_3_2 61 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 84 230 2 30 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 84 230 (Polychromatic418967fa.accept_13_7_6_9_1_1831 59 84 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 230 2 29 42 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 230
  (Polychromatic418967fa.accept_15_12_9_5_1_2973 57 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 84 230 2 28 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 84 230 (accept_3_2 55 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 84 230 2 27 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 84 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 84 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 230 2 26 42 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 84 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 84 230 2 25 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 84 230 (accept_3_2 49 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 230 2 24 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 84 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 84 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 230 2 23 42 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 84 230
  (Polychromatic418967fa.accept_16_13_4_6_1_2322 45 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 84 230 2 22 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 84 230 (accept_3_2 43 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 84 230 2 21 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 84 230 (Polychromatic418967fa.accept_13_2_6_9_1_2636 41 84 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 230 2 20 42 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 230
  (Polychromatic418967fa.accept_18_3_12_14_1_2232 39 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 84 230 2 19 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 84 230 (accept_3_2 37 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 230 2 18 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 84 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 84 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 230 2 17 42 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 84 230 2 16 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 84 230 (accept_3_2 31 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 230 2 15 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 84 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 84 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 230 2 14 42 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 84 230
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 84 230 2 13 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 84 230 (accept_3_2 25 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 230 2 12 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 84 230 (Polychromatic418967fa.accept_13_10_6_9_1_1152 23 84 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 230 2 11 42 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 230
  (Polychromatic418967fa.accept_16_5_4_6_1_3349 21 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 230 2 10 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 84 230 (accept_3_2 19 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 230 2 9 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 84 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 230 2 8 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 84 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  84 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 230 2 7 42 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 230 (accept_3_2 13
  84 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 230 2 6 42 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 84 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 84 230 2 5 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 84 230 (Polychromatic418967fa.accept_22_9_18_10_1_7319 9 84 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 230 2 4 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 230 (accept_3_2 7 84 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 84 230 2 3 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 84 230 (Polychromatic418967fa.accept_16_5_4_6_1_3349 5 84 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 230 2 2 42 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84 230 (Polychromatic418967fa.accept_11_3_7_10_1_180 3
  84 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 230 2 1 42 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 230 (accept_3_2 1 84
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 230
  (allA_succ_of_accept 82 83 230 (accept_3_2 82 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 83 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 230 (accept_3_2 79 83 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 230 (accept_3_2 76 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 230 (Polychromatic418967fa.accept_15_14_8_5_1_2104 74 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 230 (accept_3_2 73 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 230 (Polychromatic418967fa.accept_15_12_8_5_1_5048 72 83
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 230 (accept_3_2 70 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 230 (accept_3_2 67 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 83 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 230 (accept_3_2 64 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 83 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 230 (accept_3_2 61 83 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 230
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 59 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 230 (accept_3_2 58 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 230 (accept_3_2 55 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 230 (Polychromatic418967fa.accept_13_2_5_9_1_610 54 83 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 230 (accept_3_2 52 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 230 (Polychromatic418967fa.accept_16_2_3_6_1_3372 50 83 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 230 (accept_3_2 49 83 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 230
  (Polychromatic418967fa.accept_14_5_13_6_1_3574 47 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 230 (accept_3_2 46 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 83 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 230 (accept_3_2 43 83 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 230 (accept_3_2 40 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 230 (Polychromatic418967fa.accept_11_5_6_10_1_1432 38 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 230 (accept_3_2 37 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 230 (Polychromatic418967fa.accept_16_4_3_6_1_6805 36 83 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 230 (accept_3_2 34 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 230 (accept_3_2 31 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 83 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 230 (accept_3_2 28 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 83 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 230 (accept_3_2 25 83 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 230
  (Polychromatic418967fa.accept_17_6_15_9_1_1791 23 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 230 (accept_3_2 22 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 230 (accept_3_2 19 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 230 (Polychromatic418967fa.accept_15_3_8_5_1_2105 18 83 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 230 (accept_3_2 16 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 230 (Polychromatic418967fa.accept_13_1_5_9_1_226 14 83 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 230 (accept_3_2 13 83 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 83 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 230
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 230 (accept_3_2 10 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 83 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 83 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 230 (accept_3_2 7 83 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 83 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 83 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 230 (accept_3_2 4 83 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 230
  (Polychromatic418967fa.accept_13_2_5_9_1_610 2 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 230 (accept_3_2 1 83 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 230 (allA_of_3_0
  82 82 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 230 (allA_succ_of_accept 80 81 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 80 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 81 230 (accept_3_2 79 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  81 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 78 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 81 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 230 (accept_3_2 76 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 81 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 81 230
  (Polychromatic418967fa.accept_15_14_6_5_1_7215 74 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 81 230 (accept_3_2 73 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  81 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 81 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 230 (accept_3_2 70 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 230 (Polychromatic418967fa.accept_16_5_1_6_1_3367 69 81 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 81 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 68 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 230 (accept_3_2 67 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  81 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 81 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 230 (accept_3_2 64 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 81 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 230
  (Polychromatic418967fa.accept_29_4_23_27_1_13736 62 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 81 230 (accept_3_2 61 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 81 230 (Polychromatic418967fa.accept_11_5_4_10_1_524 60 81 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 81 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 230 (accept_3_2 58 81 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 230 (Polychromatic418967fa.accept_13_5_3_9_1_1189
  57 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 230
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 56 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 81 230 (accept_3_2 55 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  81 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 81 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 230 (accept_3_2 52 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 81 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 230
  (Polychromatic418967fa.accept_16_2_1_6_1_2342 50 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 230 (accept_3_2 49 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  81 230 (Polychromatic418967fa.accept_15_3_6_5_1_2079 48 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 81 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 230 (accept_3_2 46 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 81 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 230 (accept_3_2 43 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  81 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 81 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 230 (accept_3_2 40 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 81 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 230 (accept_3_2 37 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 230 (Polychromatic418967fa.accept_19_17_5_2_1_2843 36 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 230 (accept_3_2 34 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 81 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 230
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 32 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 230 (accept_3_2 31 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 230 (accept_3_2 28 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 230 (accept_3_2 25 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 230 (accept_3_2 22 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 230 (Polychromatic418967fa.accept_13_8_3_9_1_5269 21 81 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 230
  (Polychromatic418967fa.accept_13_7_3_9_1_1142 20 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 230 (accept_3_2 19 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 230 (accept_3_2 16 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 230
  (Polychromatic418967fa.accept_15_14_6_5_1_7215 14 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 230 (accept_3_2 13 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 230 (accept_3_2 10 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 81 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 230
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 8 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 230 (accept_3_2 7 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  230 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 230 (accept_3_2 4 81 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  81 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 230 (accept_3_2 1 81 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 230
  (allA_succ_of_accept 79 80 230 (accept_3_2 79 80 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 80
  230 2 39 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  77 80 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 80 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 80 230 2 38 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 75 80 230 5 15 16 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 80 230 2 37 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 80 230 (accept_3_2 73 80 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 80 230 2 36 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 80 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 71 80 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 80 230 10 7 8 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 80 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 69 80 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 80 230 2 34 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 80 230 (accept_3_2 67 80 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 80 230 2 33 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 80 230 5 13 16 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 64 80 230 2 32 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 80 230 (Polychromatic418967fa.accept_13_11_2_9_1_2640 63 80 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 80 230 2 31 40 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 80 230 (accept_3_2 61 80 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80 230 10 6 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 80 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274
  59 80 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 230 2 29 40 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 80 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 80 230 2 28 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 80 230 5 11 16 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 80 230 2 27 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 80 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 80 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 80 230 2 26 40 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 80 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 80 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 80 230 10 5 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 80 230 (accept_3_2 49 80 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80
  230 2 24 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  47 80 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 80 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 80 230 2 23 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 45 80 230 5 9 16 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 80 230 2 22 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 80 230 (accept_3_2 43 80 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 80 230 2 21 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 80 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 80 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 80 230 10 4 8 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 80 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 80 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 80 230 2 19 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 80 230 (accept_3_2 37 80 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 80 230 2 18 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 80 230 5 7 16 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 80 230 2 17 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 80 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 80 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 80 230 2 16 40 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 80 230 (accept_3_2 31 80 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 230 10 3 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 29
  80 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 80 230 2 14 40 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 80 230
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 80 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 80 230 2 13 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 80 230 5 5 16 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 80 230 2 12 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 80 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 80 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 230 2 11 40 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 80 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 230 10 2 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 230 (accept_3_2 19 80 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  230 2 9 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 80 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 230 2 8 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 80 230 5 3 16 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 80 230 2 7 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 80 230 (accept_3_2 13 80 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 80 230 2 6 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 80 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 80 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 230 10 1 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 80 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 230 2 4 40 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 230 (accept_3_2 7 80 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 230 2 3 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 80 230 5 1 16 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 80 230 2 2 40 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 80
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 230 2 1 40 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 230 (accept_3_2 1 80
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 230 (allA_of_3_0 79
  79 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 230 (allA_succ_of_accept 77 78 230
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 77 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 78 230 2 38 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 78 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 78 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 78 230 2 37 39 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 230 (accept_3_2 73 78 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 230 2 36 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 71
  78 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 230 2 35 39 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 78 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 69 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 78 230 2 34 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 78 230 (accept_3_2 67 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 78 230 2 33 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 78 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 78 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 230 2 32 39 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 78 230 2 31 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 78 230 (accept_3_2 61 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 230 2 30 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 78 230 (Polychromatic418967fa.accept_22_15_12_10_1_10700 59 78 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 230 2 29 39 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 78 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 57 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 78 230 2 28 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 78 230 (accept_3_2 55 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 230 2 27 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 78 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 78 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 230 2 26 39 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 78 230 2 25 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 78 230 (accept_3_2 49 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 230 2 24 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 78 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 78 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 230 2 23 39 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 78 230 2 22 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 78 230 (accept_3_2 43 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 230 2 21 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 78 230 (Polychromatic418967fa.accept_24_17_6_14_1_11994 41 78 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 230 2 20 39 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 78 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 78 230 2 19 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 78 230 (accept_3_2 37 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 230 2 18 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 78 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 78 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 230 2 17 39 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 230 2 16 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 78 230 (accept_3_2 31 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 230 2 15 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 78 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 78 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 230 2 14 39 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 78 230 2 13 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 78 230 (accept_3_2 25 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 230 2 12 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 78 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 78 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 230 2 11 39 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 230 2 10 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 78 230 (accept_3_2 19 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 230 2 9 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 78 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 230 2 8 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 15
  78 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 230 2 7 39 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 230 (accept_3_2 13
  78 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 230 2 6 39 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 230
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 78 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 78 230 2 5 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 78 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 78 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 230 2 4 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 230 (accept_3_2 7 78 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 78 230 2 3 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 78 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 78 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 230 2 2 39 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 78
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 230 2 1 39 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 230 (accept_3_2 1 78
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 230
  (allA_succ_of_accept 76 77 230 (accept_3_2 76 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 230 (Polychromatic418967fa.accept_15_14_2_5_1_1272 74 77 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 230 (accept_3_2 73 77 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 230 (Polychromatic418967fa.accept_15_12_2_5_1_3939 72 77
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 230 (accept_3_2 70 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 68 77 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 230 (accept_3_2 67 77 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 230 (Polychromatic418967fa.accept_19_9_1_2_1_6839 66 77 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 230
  (Polychromatic418967fa.accept_18_11_5_14_1_4560 65 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 230 (accept_3_2 64 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 230 (Polychromatic418967fa.accept_13_10_12_9_1_1837 62 77 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 230 (accept_3_2 61 77 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 230 (Polychromatic418967fa.accept_13_8_12_9_1_1168 60 77
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 230 (accept_3_2 58 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 77 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 230 (accept_3_2 55 77 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 230 (Polychromatic418967fa.accept_24_6_5_14_1_13735 54 77 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 230
  (Polychromatic418967fa.accept_19_15_1_2_1_6894 53 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 230 (accept_3_2 52 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 230 (Polychromatic418967fa.accept_14_8_7_6_1_1159 50 77 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 230 (accept_3_2 49 77 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 230 (Polychromatic418967fa.accept_15_3_2_5_1_2980 48 77 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 230 (accept_3_2 46 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 77 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 230 (accept_3_2 43 77 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 230 (Polychromatic418967fa.accept_13_3_12_9_1_1193 42 77 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 230
  (Polychromatic418967fa.accept_14_13_7_6_1_3525 41 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 230 (accept_3_2 40 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 230 (Polychromatic418967fa.accept_20_18_17_10_1_13734 38 77 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 230 (accept_3_2 37 77 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 230 (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 77
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 230 (accept_3_2 34 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 77 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 230 (accept_3_2 31 77 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 230 (Polychromatic418967fa.accept_21_9_14_20_1_4579 30 77 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 230
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 29 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 230 (accept_3_2 28 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 230 (Polychromatic418967fa.accept_15_11_2_5_1_2076 26 77 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 230 (accept_3_2 25 77 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 230 (Polychromatic418967fa.accept_25_24_2_5_1_13733 24 77
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 230 (accept_3_2 22 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 77 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 230 (accept_3_2 19 77 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 230 (Polychromatic418967fa.accept_15_3_2_5_1_2980 18 77 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 230
  (Polychromatic418967fa.accept_21_17_14_20_1_7811 17 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 77 230 (accept_3_2 16 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 77 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 77 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 230 (Polychromatic418967fa.accept_15_14_2_5_1_1272 14 77
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 230 (accept_3_2 13 77 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 230 (Polychromatic418967fa.accept_15_12_2_5_1_3939
  12 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 230 (accept_3_2 10 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 77 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 230 (accept_3_2 7 77 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 230 (Polychromatic418967fa.accept_19_6_1_2_1_12526 6 77 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 230
  (Polychromatic418967fa.accept_20_5_17_10_1_3632 5 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 230 (accept_3_2 4 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 230 (Polychromatic418967fa.accept_21_2_14_20_1_841 2 77 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 230 (accept_3_2 1 77 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 230 (allA_of_3_0 76 76 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 230 (allA_succ_of_accept 74 75
  230 (Polychromatic418967fa.accept_7_4_5_6_1_344 74 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 230 (accept_3_2 73 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 230 (Polychromatic418967fa.accept_19_15_18_2_1_6857 72 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 75 230 5 14 15 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 75 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 75 230 (Polychromatic418967fa.accept_16_4_11_6_1_5591 68 75 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 230 (accept_3_2 67 75 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 75 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 66 75 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 75 230 5 13 15 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 75 230 (accept_3_2 64 75 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 230 (Polychromatic418967fa.accept_11_8_9_10_1_503 63 75 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 62 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 230 (accept_3_2 61 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75
  230 5 12 15 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  75 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 75 230 (accept_3_2 58 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 75 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 75 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 75 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 75 230 5 11 15 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 75 230
  (Polychromatic418967fa.accept_12_6_3_2_1_743 54 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 75 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 230 (accept_3_2 52 75 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 75 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 75 230 5 10 15 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 75 230 (accept_3_2 49 75 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 230 (Polychromatic418967fa.accept_18_12_3_14_1_5919 48 75
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 230 (accept_3_2 46 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75
  230 5 9 15 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  75 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 75 230 (accept_3_2 43 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 75 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 75 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 75 230 5 8 15 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 75 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 75 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 230 (accept_3_2 37 75 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 75 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 75 230 5 7 15 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 75 230 (accept_3_2 34 75 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 230 (accept_3_2 31 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75
  230 5 6 15 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  75 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 75 230 (accept_3_2 28 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 75 230 (Polychromatic418967fa.accept_13_1_10_9_1_215 27 75 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 75 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 75 230 5 5 15 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 75 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 24 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 230 (accept_3_2 22 75 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 75 230 5 4 15 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 230 (accept_3_2 19 75 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 75 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 230 (accept_3_2 16 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75
  230 5 3 15 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  75 230 (Polychromatic418967fa.accept_13_1_10_9_1_215 14 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 75 230 (accept_3_2 13 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 230 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 75 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 230 5 2 15 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 75 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 75 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 230 (accept_3_2 7 75 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 75 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 75 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 75 230 5 1 15 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 230 (accept_3_2 4 75 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 230 (Polychromatic418967fa.accept_16_3_11_6_1_4467 3 75 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 230 (accept_3_2 1 75 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 230 (allA_succ_of_accept
  73 74 230 (accept_3_2 73 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 230 2 36 37 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 230 2 35 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 74 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 74 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 230 2 34 37 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 230 (accept_3_2 67 74 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 230 2 33 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 65
  74 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 230 2 32 37 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 230
  (Polychromatic418967fa.accept_22_19_8_10_1_12142 63 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 74 230 2 31 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 74 230 (accept_3_2 61 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 74 230 2 30 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 74 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 74 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 74 230 2 29 37 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 74 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 57 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 74 230 2 28 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 74 230 (accept_3_2 55 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 74 230 2 27 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 74 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 74 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 74 230 2 26 37 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 74 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 74 230 2 25 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 74 230 (accept_3_2 49 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 74 230 2 24 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 74 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 74 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 230 2 23 37 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 230 2 22 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 74 230 (accept_3_2 43 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 74 230 2 21 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 74 230 (Polychromatic418967fa.accept_19_3_17_2_1_6963 41 74 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 230 2 20 37 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 230 2 19 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 74 230 (accept_3_2 37 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 74 230 2 18 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 74 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 74 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 230 2 17 37 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 74 230 2 16 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 74 230 (accept_3_2 31 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 74 230 2 15 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 74 230 (Polychromatic418967fa.accept_18_11_2_14_1_3351 29 74 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 230 2 14 37 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 230
  (Polychromatic418967fa.accept_21_6_11_20_1_10794 27 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 74 230 2 13 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 74 230 (accept_3_2 25 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 74 230 2 12 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 74 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 74 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 230 2 11 37 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 230 2 10 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 74 230 (accept_3_2 19 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 74 230 2 9 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 74 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 74 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 230 2 8 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 15
  74 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 230 2 7 37 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 230 (accept_3_2 13
  74 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 230 2 6 37 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74 230
  (Polychromatic418967fa.accept_18_11_2_14_1_3351 11 74 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 74 230 2 5 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 74 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 74 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 230 2 4 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 230 (accept_3_2 7 74 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 74 230 2 3 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 74 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 74 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 230 2 2 37 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 74
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 230 2 1 37 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 230 (accept_3_2 1 74
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 230 (allA_of_3_0 73 73 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 230 (allA_succ_of_accept 71 72 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 72 230 2 35 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 72 230 (Polychromatic418967fa.accept_13_4_7_9_1_5260 69 72 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 230 2 34 36 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 230 (accept_3_2 67 72 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 230 2 33 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 230 (Polychromatic418967fa.accept_17_14_4_9_1_2792
  65 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 230 2 32 36 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 230
  (Polychromatic418967fa.accept_13_11_7_9_1_612 63 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 72 230 2 31 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 72 230 (accept_3_2 61 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 230 2 30 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 72 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 72 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 230 2 29 36 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 72 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 72 230 2 28 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 72 230 (accept_3_2 55 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 230 2 27 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 72 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 72 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 230 2 26 36 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 72 230
  (Polychromatic418967fa.accept_15_6_12_5_1_2108 51 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 72 230 2 25 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 72 230 (accept_3_2 49 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 72 230 2 24 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 72 230 (Polychromatic418967fa.accept_13_8_7_9_1_611 47 72 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 230 2 23 36 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 230 2 22 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 72 230 (accept_3_2 43 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 230 2 21 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 72 230 (Polychromatic418967fa.accept_13_2_7_9_1_2616 41 72 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72 230 2 20 36 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 72 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 72 230 2 19 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 72 230 (accept_3_2 37 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 230 2 18 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 72 230 (Polychromatic418967fa.accept_20_15_12_10_1_1291 35 72 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 230 2 17 36 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 230
  (Polychromatic418967fa.accept_20_13_12_10_1_3619 33 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 72 230 2 16 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 72 230 (accept_3_2 31 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 72 230 2 15 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 72 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 72 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 230 2 14 36 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 230
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 72 230 2 13 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 72 230 (accept_3_2 25 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 230 2 12 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 72 230 (Polychromatic418967fa.accept_15_8_12_5_1_2987 23 72 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 230 2 11 36 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 230
  (Polychromatic418967fa.accept_13_8_7_9_1_611 21 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 230 2 10 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 72 230 (accept_3_2 19 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 230 2 9 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 72 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 230 2 8 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 72 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  72 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 230 2 7 36 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 230 (accept_3_2 13
  72 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 230 2 6 36 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 72 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 72 230 2 5 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 72 230 (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 72 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 230 2 4 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 230 (accept_3_2 7 72 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 72 230 2 3 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 72 230 (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 72 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 230 2 2 36 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 72
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 230 2 1 36 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 230 (accept_3_2 1 72
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 230 (allA_succ_of_accept 70
  71 230 (accept_3_2 70 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 71 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 71 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 71 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 230 (accept_3_2 67 71 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 71 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 65
  71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 71 230 (accept_3_2 64 71
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 71 230 (Polychromatic418967fa.accept_6_3_5_2_1_12
  63 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 71 230
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 62 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 71 230 (accept_3_2 61 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  71 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 71 230 (Polychromatic418967fa.accept_11_4_5_10_1_926 59 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 71 230 (accept_3_2 58 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 71 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 71 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 71 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 71 230 (accept_3_2 55 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  71 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 71 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 230 (accept_3_2 52 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 71 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 230
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 50 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 71 230 (accept_3_2 49 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  71 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 71 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 230 (accept_3_2 46 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 71 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 71 230 (accept_3_2 43 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  71 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 230 (accept_3_2 40 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 230 (accept_3_2 37 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 230 (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 230 (Polychromatic418967fa.accept_14_7_1_6_1_3514 35 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 230 (accept_3_2 34 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 71 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 230
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 230 (accept_3_2 31 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 230 (accept_3_2 28 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 230 (accept_3_2 25 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 230 (accept_3_2 22 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 71 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 230 (accept_3_2 19 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 230 (Polychromatic418967fa.accept_17_1_3_9_1_958 18 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 230 (accept_3_2 16 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 230
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 14 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 230 (accept_3_2 13 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 230 (accept_3_2 10 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 230
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 230 (accept_3_2 7 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  230 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 230 (accept_3_2 4 71 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  71 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 230 (accept_3_2 1 71 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 230 (allA_of_3_0 70 70 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 230 (allA_succ_of_accept 68 69 230
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 68 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 230 (accept_3_2 67 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 230 (accept_3_2 64 69 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 69 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 230 (accept_3_2 61 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 230 (Polychromatic418967fa.accept_13_8_4_9_1_1145 60 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 69 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 230 (accept_3_2 58 69 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 69 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 230
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 230 (accept_3_2 55 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 230 (accept_3_2 52 69 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 69 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 230
  (Polychromatic418967fa.accept_22_6_3_10_1_12182 50 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 230 (accept_3_2 49 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 69 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 69 230 23 2 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 69 230 (Polychromatic418967fa.accept_13_6_4_9_1_4326
  45 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 230 (accept_3_2 43 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 230 (accept_3_2 40 69 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 230
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 230 (accept_3_2 37 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 230 (Polychromatic418967fa.accept_16_4_5_6_1_8071 36 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 69 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 230 (accept_3_2 34 69 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 230 (Polychromatic418967fa.accept_13_7_4_9_1_1865 33 69 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 230
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 32 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 230 (accept_3_2 31 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 230 (accept_3_2 28 69 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 230 (accept_3_2 25 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 230 (Polychromatic418967fa.accept_21_3_6_20_1_9278 24 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 23 69 230 23 1 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 22 69 230 (accept_3_2 22 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 69 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 69 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 69 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 230 (accept_3_2 19 69 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 230 (Polychromatic418967fa.accept_11_7_3_10_1_1461
  18 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 230 (accept_3_2 16 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  69 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 69 230 (Polychromatic418967fa.accept_15_14_9_5_1_3932 14 69 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 230 (accept_3_2 13 69 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 69 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 230 (accept_3_2 10 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  69 230 (Polychromatic418967fa.accept_19_9_12_2_1_9776 9 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 69 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 69 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 230 (accept_3_2 7 69 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 69 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 230 (accept_3_2 4 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69
  230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 69 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 230 (accept_3_2 1 69 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 69 230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 230
  (allA_succ_of_accept 67 68 230 (accept_3_2 67 68 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68
  230 2 33 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  65 68 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 65 68 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 68 230 2 32 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 68 230 (Polychromatic418967fa.accept_15_3_8_5_1_2105 63 68 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 230 2 31 34 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 230 (accept_3_2 61 68 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 230 2 30 34 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 230
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 68 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 68 230 2 29 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 68 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 68 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 68 230 2 28 34 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 68 230 (accept_3_2 55 68 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68 230 2 27 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 68 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 53
  68 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 68 230 2 26 34 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 68 230
  (Polychromatic418967fa.accept_13_12_3_9_1_4341 51 68 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 68 230 2 25 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 68 230 (accept_3_2 49 68 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 68 230 2 24 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 68 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 68 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 68 230 2 23 34 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 68 230
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 45 68 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 68 230 2 22 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 68 230 (accept_3_2 43 68 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 68 230 2 21 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 68 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 68 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 68 230 2 20 34 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 68 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 68 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 68 230 2 19 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 68 230 (accept_3_2 37 68 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 68 230 2 18 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 68 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 68 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 230 2 17 34 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 230
  (Polychromatic418967fa.accept_13_7_3_9_1_1142 33 68 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 230 2 16 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 68 230 (accept_3_2 31 68 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 68 230 2 15 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 68 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 68 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 68 230 2 14 34 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 68 230
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 68 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 68 230 2 13 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 68 230 (accept_3_2 25 68 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 68 230 2 12 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 68 230 (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 68 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 230 2 11 34 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 230
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 21 68 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 230 2 10 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 68 230 (accept_3_2 19 68 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 68 230 2 9 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 68 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 68 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 230 2 8 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 15
  68 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 230 2 7 34 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 230 (accept_3_2 13
  68 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 230 2 6 34 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 68 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 68 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 68 230 2 5 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 68 230 (Polychromatic418967fa.accept_19_9_11_2_1_5436 9 68 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 230 2 4 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 230 (accept_3_2 7 68 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 68 230 2 3 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 68 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 68 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 230 2 2 34 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 230 (Polychromatic418967fa.accept_15_3_8_5_1_2105 3
  68 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 230 2 1 34 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 230 (accept_3_2 1 68
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 230 (allA_of_3_0 67 67 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 230 (allA_succ_of_accept 65 66 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 65 66 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 230 2 32 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 66 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 63 66 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 230 2 31 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 230 (accept_3_2 61 66 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 230 2 30 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 230 (Polychromatic418967fa.accept_14_3_10_6_1_1136
  59 66 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 230 2 29 33 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 66 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 230 2 28 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 66 230 (accept_3_2 55 66 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 230 2 27 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 66 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 66 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 230 2 26 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 66 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 66 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 66 230 2 25 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 66 230 (accept_3_2 49 66 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 230 2 24 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 66 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 66 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 230 2 23 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 66 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 230 2 22 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 66 230 (accept_3_2 43 66 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 230 2 21 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 66 230 (Polychromatic418967fa.accept_13_2_1_9_1_1174 41 66 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 230 2 20 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 66 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 230 2 19 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 66 230 (accept_3_2 37 66 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 230 2 18 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 66 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 66 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 230 2 17 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 66 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 66 230 2 16 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 66 230 (accept_3_2 31 66 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 230 2 15 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 66 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 66 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 230 2 14 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 66 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 230 2 13 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 66 230 (accept_3_2 25 66 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 230 2 12 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 66 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 66 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 230 2 11 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 66 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 230 2 10 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 66 230 (accept_3_2 19 66 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 230 2 9 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 66 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 230 2 8 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  66 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 230 2 7 33 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 230 (accept_3_2 13
  66 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 230 2 6 33 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 66 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 230 2 5 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 66 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 66 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 230 2 4 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 230 (accept_3_2 7 66 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 66 230 2 3 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 66 230 (Polychromatic418967fa.accept_13_5_1_9_1_618 5 66 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 230 2 2 33 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 3
  66 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 230 2 1 33 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 230 (accept_3_2 1 66
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 230 (allA_succ_of_accept 64 65 230
  (accept_3_2 64 65 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 65 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 65 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 230 (accept_3_2 61 65 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 65 230 5 12 13 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 65 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 65 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 230 (accept_3_2 58 65 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 65 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 65 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 65 230 5 11 13 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 65 230 (Polychromatic418967fa.accept_20_14_5_10_1_3647 54 65 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 65 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 230 (accept_3_2 52 65 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  65 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 65 230 5 10 13 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 65 230 (accept_3_2 49
  65 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 48 65 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 65 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 65 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 230 (accept_3_2 46 65 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 65 230 5 9 13 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 65 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 65 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 230 (accept_3_2 43 65 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 65 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 230
  (Polychromatic418967fa.accept_18_5_11_14_1_7203 41 65 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 65 230 5 8 13 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 65 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 65 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 65 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 230 (accept_3_2 37 65 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 36
  65 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 65 230 5 7 13 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 65 230 (accept_3_2 34
  65 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 230
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 65 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 65 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 230 (accept_3_2 31 65 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 65 230 5 6 13 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 65 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 65 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 230 (accept_3_2 28 65 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 65 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 65 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 65 230 5 5 13 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 65 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 65 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 65 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 230 (accept_3_2 22 65 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  65 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 65 230 5 4 13 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 65 230 (accept_3_2 19
  65 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 65 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 65 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 65 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 230 (accept_3_2 16 65 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 65 230 5 3 13 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 65 230 (Polychromatic418967fa.accept_19_14_8_2_1_6846 14 65 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 230 (accept_3_2 13 65 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 65 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 65 230 5 2 13 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 65 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 65 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 230 (accept_3_2 7 65 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  65 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 65 230 5 1 13 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 65 230 (accept_3_2 4 65
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 230 (Polychromatic418967fa.accept_4_3_1_2_1_62
  3 65 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 230
  (Polychromatic418967fa.accept_16_2_1_6_1_2342 2 65 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 230 (accept_3_2 1 65 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 230 (allA_of_3_0 64 64 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 230 (allA_succ_of_accept 62 63 230
  (Polychromatic418967fa.accept_15_2_3_5_1_2991 62 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 230 (accept_3_2 61 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 230 (Polychromatic418967fa.accept_13_8_11_9_1_593 60 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 230 (accept_3_2 58 63 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 63 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 230
  (Polychromatic418967fa.accept_17_5_12_9_1_10091 56 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 230 (accept_3_2 55 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 63 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 230 (accept_3_2 52 63 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 230 (Polychromatic418967fa.accept_15_6_3_5_1_607 51 63 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 230
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 50 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 230 (accept_3_2 49 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 230 (Polychromatic418967fa.accept_17_14_12_9_1_2774 48 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 230 (accept_3_2 46 63 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 230
  (Polychromatic418967fa.accept_25_19_13_5_1_13732 44 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 63 230 (accept_3_2 43 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 63 230 (Polychromatic418967fa.accept_11_9_8_10_1_934 42 63 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 63 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 230 (accept_3_2 40 63 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 230 (Polychromatic418967fa.accept_15_9_3_5_1_2077
  39 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 230
  (Polychromatic418967fa.accept_15_8_3_5_1_608 38 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 230 (accept_3_2 37 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 230 (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 230 (accept_3_2 34 63 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 230
  (Polychromatic418967fa.accept_15_2_3_5_1_2991 32 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 230 (accept_3_2 31 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 63 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 230 (accept_3_2 28 63 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 230 (Polychromatic418967fa.accept_13_1_11_9_1_1857 27 63 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 230
  (Polychromatic418967fa.accept_25_1_13_5_1_10205 26 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 230 (accept_3_2 25 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 230 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 230 (accept_3_2 22 63 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 230
  (Polychromatic418967fa.accept_11_9_8_10_1_934 20 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 230 (accept_3_2 19 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 230 (accept_3_2 16 63 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 230 (Polychromatic418967fa.accept_13_2_11_9_1_591 15 63 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 230
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 14 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 230 (accept_3_2 13 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 230 (Polychromatic418967fa.accept_19_12_6_2_1_5424 12 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 230 (accept_3_2 10 63 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 230
  (Polychromatic418967fa.accept_13_8_11_9_1_593 8 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 230 (accept_3_2 7 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  230 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 230 (accept_3_2 4 63 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 230 (Polychromatic418967fa.accept_18_3_9_14_1_2219 3 63 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 230 (Polychromatic418967fa.accept_13_2_11_9_1_591 2
  63 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 230 (accept_3_2 1 63 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 230 (allA_succ_of_accept 61 62 230
  (accept_3_2 61 62 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 230 2 30 31 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 230
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 59 62 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 230 2 29 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 62 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 62 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 230 2 28 31 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 230 (accept_3_2 55 62 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 230 2 27 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 230 (Polychromatic418967fa.accept_13_1_10_9_1_215
  53 62 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 230 2 26 31 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 62 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 230 2 25 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 62 230 (accept_3_2 49 62 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 62 230 2 24 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 62 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 62 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 230 2 23 31 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 230
  (Polychromatic418967fa.accept_13_6_10_9_1_4329 45 62 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 230 2 22 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 62 230 (accept_3_2 43 62 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 62 230 2 21 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 62 230 (Polychromatic418967fa.accept_15_11_2_5_1_2076 41 62 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 62 230 2 20 31 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 62 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 62 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 62 230 2 19 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 62 230 (accept_3_2 37 62 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 62 230 2 18 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 62 230 (Polychromatic418967fa.accept_19_16_5_2_1_8375 35 62 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 230 2 17 31 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 62 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 230 2 16 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 62 230 (accept_3_2 31 62 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 62 230 2 15 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 62 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 62 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 230 2 14 31 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 230
  (Polychromatic418967fa.accept_13_1_10_9_1_215 27 62 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 230 2 13 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 62 230 (accept_3_2 25 62 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 62 230 2 12 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 62 230 (Polychromatic418967fa.accept_18_5_8_14_1_1282 23 62 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 62 230 2 11 31 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 62 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 62 230 2 10 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 62 230 (accept_3_2 19 62 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 62 230 2 9 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 62 230 (Polychromatic418967fa.accept_19_17_5_2_1_2843 17 62 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 230 2 8 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 15
  62 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 230 2 7 31 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 230 (accept_3_2 13
  62 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 230 2 6 31 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 62 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 62 230 2 5 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 62 230 (Polychromatic418967fa.accept_22_9_18_10_1_7319 9 62 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 230 2 4 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 230 (accept_3_2 7 62 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 230 2 3 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 230 (Polychromatic418967fa.accept_18_5_8_14_1_1282 5 62 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 230 2 2 31 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 62
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 230 2 1 31 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 230 (accept_3_2 1 62
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 230 (allA_of_3_0 61 61 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 230 (allA_succ_of_accept 59 60 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 60 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 230 2 29 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 60 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 60 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 230 2 28 30 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 60 230 5 11 12 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 60 230 2 27 30 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 60 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 60 230 2 26 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 60 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 60 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 230 10 5 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 230 (accept_3_2 49 60 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 230 2 24 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 60 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 230 2 23 30 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 230 5 9 12 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 230 2 22 30 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 230
  (accept_3_2 43 60 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 230 2 21 30 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 230
  (Polychromatic418967fa.accept_26_15_8_22_1_13731 41 60 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 60 230 10 4 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 60 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 60 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 230 2 19 30 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 230 (accept_3_2 37 60 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 230 2 18 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 60 230 5 7 12 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 60 230 2 17 30 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 60 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 230 2 16 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 60 230 (accept_3_2 31 60 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 230 10 3 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 60 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 230 2 14 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 60 230 (Polychromatic418967fa.accept_13_1_8_9_1_1154
  27 60 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 230 2 13 30 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 60 230 5 5 12 46
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 60 230 2 12 30
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 60 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 60 230 2 11 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 60 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 60 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 230 10 2 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 230 (accept_3_2 19 60 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 230 2 9 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 60 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 230 2 8 30 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60 230 5 3 12 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60 230 2 7 30 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 230 (accept_3_2 13
  60 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 230 2 6 30 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 230
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 60 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 60 230 10 1 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 60 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 60 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 230 2 4 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 230 (accept_3_2 7 60 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 60 230 2 3 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 5 60 230 5 1 12 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 4 60 230 2 2 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 60 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 60 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 230 2 1 30 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 230 (accept_3_2 1 60 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 60 230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 230
  (allA_succ_of_accept 58 59 230 (accept_3_2 58 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 59 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 230 (accept_3_2 55 59 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 230 (Polychromatic418967fa.accept_13_2_7_9_1_2616 54 59 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 230 (accept_3_2 52 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 230 (Polychromatic418967fa.accept_13_11_7_9_1_612 50 59 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 230 (accept_3_2 49 59 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 230 (Polychromatic418967fa.accept_22_4_15_10_1_13730 48 59 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 230
  (Polychromatic418967fa.accept_13_8_7_9_1_611 47 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 230 (accept_3_2 46 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 59 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 230 (accept_3_2 43 59 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 230 (Polychromatic418967fa.accept_13_3_7_9_1_1153 42 59 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 230 (accept_3_2 40 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 230 (Polychromatic418967fa.accept_11_5_4_10_1_524 38 59 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 230 (accept_3_2 37 59 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 230 (Polychromatic418967fa.accept_15_6_14_5_1_2976 36 59 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 230
  (Polychromatic418967fa.accept_16_3_11_6_1_4467 35 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 230 (accept_3_2 34 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 59 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 230 (accept_3_2 31 59 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 59 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 230 (accept_3_2 28 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 230 (Polychromatic418967fa.accept_18_8_5_14_1_3353 26 59 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 230 (accept_3_2 25 59 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 230 (Polychromatic418967fa.accept_13_11_7_9_1_612 24 59 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 230 (accept_3_2 22 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 59 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 230 (accept_3_2 19 59 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 59 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 230 (accept_3_2 16 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 230 (Polychromatic418967fa.accept_21_14_17_20_1_12259 14 59 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 230 (accept_3_2 13 59 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 230 (Polychromatic418967fa.accept_22_12_15_10_1_12144 12 59
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 230 (accept_3_2 10 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 59 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 230 (accept_3_2 7 59 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 230 (Polychromatic418967fa.accept_13_6_7_9_1_1848 6 59 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 230 (accept_3_2 4 59 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 230 (accept_3_2 1 59 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 230 (allA_of_3_0 58 58 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 57 230 (allA_succ_of_accept 56 57 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 230 (accept_3_2 55 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 230 (accept_3_2 52 57 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 57 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 230
  (Polychromatic418967fa.accept_16_2_9_6_1_4441 50 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 230 (accept_3_2 49 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 230 (Polychromatic418967fa.accept_18_12_3_14_1_5919 48 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 57 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 230 (accept_3_2 46 57 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 230 (Polychromatic418967fa.accept_11_1_2_10_1_1426 45 57 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 230 (accept_3_2 43 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 230 (accept_3_2 40 57 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 230 (accept_3_2 37 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 230 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 57 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 230 (accept_3_2 34 57 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 57 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 230
  (Polychromatic418967fa.accept_15_2_12_5_1_2107 32 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 230 (accept_3_2 31 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 230 (accept_3_2 28 57 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 230 (accept_3_2 25 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 230 (accept_3_2 22 57 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 230 (Polychromatic418967fa.accept_14_7_1_6_1_3514 21 57 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 230 (accept_3_2 19 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 230 (accept_3_2 16 57 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 230
  (Polychromatic418967fa.accept_13_1_5_9_1_226 14 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 230 (accept_3_2 13 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 230 (accept_3_2 10 57 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 57 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 230 (accept_3_2 7 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  230 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 230 (accept_3_2 4 57 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  57 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 230 (accept_3_2 1 57 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 230 (allA_succ_of_accept 55 56 230 (accept_3_2 55 56 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 230 2 27 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 56 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 56 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 230 2 26 28 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 56 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 56 230 2 25 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 56 230 (accept_3_2 49 56 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 56 230 2 24 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 56 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 56 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 56 230 2 23 28 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 56 230
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 45 56 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 56 230 2 22 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 56 230 (accept_3_2 43 56 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 56 230 2 21 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 56 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 56 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 230 2 20 28 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 56 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 230 2 19 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 56 230 (accept_3_2 37 56 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 56 230 2 18 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 56 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 56 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 230 2 17 28 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 56 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 230 2 16 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 56 230 (accept_3_2 31 56 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 56 230 2 15 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 56 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 56 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 230 2 14 28 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 230
  (Polychromatic418967fa.accept_21_6_14_20_1_4594 27 56 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 56 230 2 13 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 56 230 (accept_3_2 25 56 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 56 230 2 12 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 56 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 56 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 230 2 11 28 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 56 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 230 2 10 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 56 230 (accept_3_2 19 56 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 56 230 2 9 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 56 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 230 2 8 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 15
  56 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 230 2 7 28 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 230 (accept_3_2 13
  56 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 230 2 6 28 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56 230
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 56 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 56 230 2 5 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 56 230 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 56 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 230 2 4 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 230 (accept_3_2 7 56 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 56 230 2 3 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 56 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 56 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 230 2 2 28 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 56
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 230 2 1 28 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 230 (accept_3_2 1 56
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 230))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 230 (allA_of_3_0 55 55 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 230
  (allA_succ_of_accept 53 54 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 54 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 230 2 26 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 54 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 51
  54 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 230 2 25 27 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 230 (accept_3_2 49
  54 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 230 2 24 27 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 230
  (Polychromatic418967fa.accept_25_22_4_5_1_13729 47 54 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 54 230 2 23 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 54 230 (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 54 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 230 2 22 27 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 230 (accept_3_2 43 54 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 230 2 21 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 230 (Polychromatic418967fa.accept_14_13_12_6_1_2735
  41 54 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 230 2 20 27 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 54 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 54 230 2 19 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 54 230 (accept_3_2 37 54 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 230 2 18 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 54 230 (Polychromatic418967fa.accept_17_1_3_9_1_958 35 54 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 230 2 17 27 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 54 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 54 230 2 16 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 54 230 (accept_3_2 31 54 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 230 2 15 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 54 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 54 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 230 2 14 27 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 54 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 230 2 13 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 54 230 (accept_3_2 25 54 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 230 2 12 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 230 (Polychromatic418967fa.accept_17_6_3_9_1_7739 23 54 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 230 2 11 27 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 54 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 54 230 2 10 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 54 230 (accept_3_2 19 54 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 230 2 9 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 230 (Polychromatic418967fa.accept_19_17_16_2_1_8390 17 54 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 230 2 8 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 15
  54 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 230 2 7 27 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 230 (accept_3_2 13
  54 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 230 2 6 27 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 54 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 54 230 2 5 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 54 230 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 54 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 230 2 4 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 230 (accept_3_2 7 54 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 54 230 2 3 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 54 230 (Polychromatic418967fa.accept_13_5_2_9_1_1195 5 54 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 230 2 2 27 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 3
  54 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 230 2 1 27 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 230 (accept_3_2 1 54
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 230))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 230 (allA_succ_of_accept 52 53 230 (accept_3_2 52 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 53 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 53 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 53 230 (Polychromatic418967fa.accept_13_11_1_9_1_1179 50 53
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 230 (accept_3_2 49 53 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 48
  53 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 230 (accept_3_2 46 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 53 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 230 (accept_3_2 43 53 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 53 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 230
  (Polychromatic418967fa.accept_11_8_9_10_1_503 41 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 230 (accept_3_2 40 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 53 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 230 (accept_3_2 37 53 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 230 (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 53 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 230 (accept_3_2 34 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 53 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 230 (accept_3_2 31 53 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 53 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 230 (accept_3_2 28 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 53 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 230 (accept_3_2 25 53 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 53 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 230 (accept_3_2 22 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 53 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 230 (accept_3_2 19 53 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 230 (Polychromatic418967fa.accept_13_5_1_9_1_618 18 53 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 230 (accept_3_2 16 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 230 (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 53 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 230 (accept_3_2 13 53 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 53 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 230 (accept_3_2 10 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 230 (Polychromatic418967fa.accept_11_8_9_10_1_503 8 53 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 230 (accept_3_2 7 53 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 53 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 230 (accept_3_2 4 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 53 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 230 (accept_3_2 1 53 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 230))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 230 (allA_of_3_0 52 52
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 230 (allA_succ_of_accept 50 51 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 230 (accept_3_2 49 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 51 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 230 (accept_3_2 46 51 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 51 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 230 (accept_3_2 43 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 51 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 230 (accept_3_2 40 51 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 51 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 230 (accept_3_2 37 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 230 (accept_3_2 34 51 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 230 (accept_3_2 31 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 230 (accept_3_2 28 51 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 230 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 51 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 230 (accept_3_2 25 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 230 (accept_3_2 22 51 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 230
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 230 (accept_3_2 19 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 230 (accept_3_2 16 51 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 51 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 230
  (Polychromatic418967fa.accept_11_3_7_10_1_180 14 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 230 (accept_3_2 13 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 230 (accept_3_2 10 51 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 230 (accept_3_2 7 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  230 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 51 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 230 (accept_3_2 4 51 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 51 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  51 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 230 (accept_3_2 1 51 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 230)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 230 (allA_succ_of_accept 49 50 230 (accept_3_2 49 50 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 50 230 2 24 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 50 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 50 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 50 230 2 23 25 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 50 230 5 9 10 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 50 230 2 22 25 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 230 (accept_3_2 43 50 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 230 2 21 25 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 230
  (Polychromatic418967fa.accept_13_2_11_9_1_591 41 50 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 230 10 4 5 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 230 (Polychromatic418967fa.accept_19_1_12_2_1_6918 39 50 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 230 2 19 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 230 (accept_3_2 37 50 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 230 2 18 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 50 230 5 7 10 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 50 230 2 17 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 33
  50 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 230 2 16 25 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 230 (accept_3_2 31
  50 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 230 10 3 5 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 230
  (Polychromatic418967fa.accept_19_10_12_2_1_6948 29 50 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 50 230 2 14 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 50 230 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 50 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 230 2 13 25 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 50 230 5 5 10 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 50 230 2 12 25 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 50 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 230 2 11 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 50 230 (Polychromatic418967fa.accept_13_8_11_9_1_593 21 50 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 230 10 2 5 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 230 (accept_3_2 19 50 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 230 2 9 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 50 230 (Polychromatic418967fa.accept_16_1_2_6_1_2295 17 50 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 230 2 8 25 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 50 230 5 3 10 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 50 230 2 7 25 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 230 (accept_3_2 13
  50 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 230 2 6 25 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 230
  (Polychromatic418967fa.accept_16_11_2_6_1_1435 11 50 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 230 10 1 5 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 50 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 230 2 4 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 230 (accept_3_2 7 50 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 50 230 2 3 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 5 50 230 5 1 10 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 4 50 230 2 2 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 50 230 (Polychromatic418967fa.accept_16_3_2_6_1_4461 3 50 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 230 2 1 25 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 230 (accept_3_2 1 50 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 50 230)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 230 (allA_of_3_0
  49 49 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 230 (allA_succ_of_accept 47 48 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 48 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 230 2 23 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 48 230 (Polychromatic418967fa.accept_20_5_8_10_1_11026 45 48 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 230 2 22 24 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 230 (accept_3_2 43 48 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 230 2 21 24 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 230
  (Polychromatic418967fa.accept_25_16_23_5_1_10293 41 48 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 48 230 2 20 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 48 230 (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 48 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 230 2 19 24 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 230 (accept_3_2 37 48 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 230 2 18 24 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 48 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 48 230 2 17 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 48 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 48 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 230 2 16 24 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 230 (accept_3_2 31 48 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 230 2 15 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 29
  48 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 230 2 14 24 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 230
  (Polychromatic418967fa.accept_11_5_4_10_1_524 27 48 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 48 230 2 13 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 48 230 (accept_3_2 25 48 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 230 2 12 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 48 230 (Polychromatic418967fa.accept_15_8_3_5_1_608 23 48 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 230 2 11 24 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 230
  (Polychromatic418967fa.accept_15_6_3_5_1_607 21 48 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 230 2 10 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 48 230 (accept_3_2 19 48 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 230 2 9 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 48 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 230 2 8 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 48 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  48 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 230 2 7 24 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 230 (accept_3_2 13
  48 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 230 2 6 24 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 48 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 48 230 2 5 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 48 230 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 48 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 230 2 4 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 230 (accept_3_2 7 48 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 48 230 2 3 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 48 230 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 48 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 230 2 2 24 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48 230 (Polychromatic418967fa.accept_18_3_12_14_1_2232
  3 48 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 230 2 1 24 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 230 (accept_3_2 1 48
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 230))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 47 230 (allA_succ_of_accept 46 47 230 (accept_3_2 46 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 47 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 47 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 47 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 230 (accept_3_2 43 47 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 42
  47 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 230 (accept_3_2 40 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 230 (Polychromatic418967fa.accept_13_12_8_9_1_1833 38 47 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 230 (accept_3_2 37 47 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 47 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 230 (accept_3_2 34 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 47 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 230 (accept_3_2 31 47 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 47 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 230 (accept_3_2 28 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 47 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 230 (accept_3_2 25 47 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 47 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 230
  (Polychromatic418967fa.accept_16_7_15_6_1_1428 23 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 230 (accept_3_2 22 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 47 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 230 (accept_3_2 19 47 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 47 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 230 (accept_3_2 16 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 230 (Polychromatic418967fa.accept_13_1_8_9_1_1154 14 47 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 230 (accept_3_2 13 47 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 47 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 230 (accept_3_2 10 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 47 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 47 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 230 (accept_3_2 7 47 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 47 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 47 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 230 (accept_3_2 4 47 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 230
  (Polychromatic418967fa.accept_18_2_11_14_1_69 2 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 230 (accept_3_2 1 47 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  230))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 230 (allA_of_3_0 46 46 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 45 230 (allA_succ_of_accept 44 45 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 45
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 230 (accept_3_2 43 45 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 230 (Polychromatic418967fa.accept_11_9_1_10_1_920
  42 45 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 45 230 5 8 9 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 45 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 45 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 230 (Polychromatic418967fa.accept_14_10_3_6_1_2728 38 45
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 230 (accept_3_2 37 45 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 230 (Polychromatic418967fa.accept_13_10_6_9_1_1152
  36 45 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 45 230 5 7 9 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 230 (accept_3_2 34
  45 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 230
  (Polychromatic418967fa.accept_13_7_6_9_1_1831 33 45 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 45 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 45 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 230 (accept_3_2 31 45 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 45 230 5 6 9 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 45 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 230 (accept_3_2 28 45 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 230
  (Polychromatic418967fa.accept_20_6_5_10_1_3531 26 45 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 45 230 5 5 9 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 45 230 (Polychromatic418967fa.accept_11_2_1_10_1_196 24 45 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 230 (accept_3_2 22 45 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 230 (Polychromatic418967fa.accept_18_3_9_14_1_2219
  21 45 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 45 230 5 4 9 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 45 230 (accept_3_2 19
  45 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 45 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 230 (accept_3_2 16 45 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 45 230 5 3 9 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 45 230 (Polychromatic418967fa.accept_13_1_6_9_1_1197 14 45 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 230 (accept_3_2 13 45 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 230 (Polychromatic418967fa.accept_20_12_5_10_1_9540 12 45 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 45 230 5 2 9 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 45 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 45 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 230 (Polychromatic418967fa.accept_17_8_11_9_1_5099 8 45 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 230 (accept_3_2 7 45 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 6
  45 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 45 230 5 1 9 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 45 230 (accept_3_2 4 45
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 230 (Polychromatic418967fa.accept_4_3_1_2_1_62
  3 45 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 45 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 45 230 (accept_3_2 1 45 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  230))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 230 (allA_succ_of_accept 43 44 230 (accept_3_2 43 44
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 230 2 21 22 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 230
  (Polychromatic418967fa.accept_12_5_8_2_1_309 41 44 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 44 230 2 20 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 44 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 44 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 230 2 19 22 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 230 (accept_3_2 37 44 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 230 2 18 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274
  35 44 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 230 2 17 22 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 44 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 230 2 16 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 44 230 (accept_3_2 31 44 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 44 230 2 15 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 44 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 44 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 230 2 14 22 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 230
  (Polychromatic418967fa.accept_13_1_5_9_1_226 27 44 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 230 2 13 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 44 230 (accept_3_2 25 44 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 44 230 2 12 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 44 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 44 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 230 2 11 22 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 44 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 44 230 2 10 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 44 230 (accept_3_2 19 44 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 44 230 2 9 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 44 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 44 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 230 2 8 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  44 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 230 2 7 22 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 230 (accept_3_2 13
  44 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 230 2 6 22 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 44 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 44 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 44 230 2 5 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 44 230 (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 44 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 230 2 4 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 230 (accept_3_2 7 44 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 44 230 2 3 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 44 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 44 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 230 2 2 22 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 44
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 230 2 1 22 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 230 (accept_3_2 1 44
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 230)))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  43 230 (allA_of_3_0 43 43 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 230 (allA_succ_of_accept 41 42
  230 (Polychromatic418967fa.accept_11_8_9_10_1_503 41 42 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 42 230 2 20 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 42 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 42 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 230 2 19 21 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 230 (accept_3_2 37 42 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 230 2 18 21 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 42 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 42 230 2 17 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 42 230 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 42 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 230 2 16 21 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 230 (accept_3_2 31 42 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 230 2 15 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 29
  42 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 230 2 14 21 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 42 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 42 230 2 13 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 42 230 (accept_3_2 25 42 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 230 2 12 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 42 230 (Polychromatic418967fa.accept_11_1_9_10_1_184 23 42 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 230 2 11 21 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 42 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 230 2 10 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 42 230 (accept_3_2 19 42 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 230 2 9 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 42 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 230 2 8 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 15
  42 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 230 2 7 21 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 230 (accept_3_2 13
  42 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 230 2 6 21 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 230
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 42 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 42 230 2 5 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 42 230 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 42 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 230 2 4 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 230 (accept_3_2 7 42 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 42 230 2 3 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 42 230 (Polychromatic418967fa.accept_13_5_3_9_1_1189 5 42 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 230 2 2 21 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 42
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 230 2 1 21 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 230 (accept_3_2 1 42
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 230)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41
  230 (allA_succ_of_accept 40 41 230 (accept_3_2 40 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 41 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 230 (Polychromatic418967fa.accept_15_8_11_5_1_169 38 41 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 230 (accept_3_2 37 41 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 230 (Polychromatic418967fa.accept_15_6_11_5_1_168 36 41 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 230 (accept_3_2 34 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 41 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 230 (accept_3_2 31 41 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 230 (Polychromatic418967fa.accept_19_11_3_2_1_12485 30 41 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 230
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 29 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 230 (accept_3_2 28 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 230 (Polychromatic418967fa.accept_14_12_13_6_1_1140 26 41 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 230 (accept_3_2 25 41 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 230 (Polychromatic418967fa.accept_13_11_2_9_1_2640 24 41
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 230 (accept_3_2 22 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 230 (Polychromatic418967fa.accept_11_9_8_10_1_934 20 41 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 230 (accept_3_2 19 41 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 230 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 41 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 230
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 230 (accept_3_2 16 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 230 (Polychromatic418967fa.accept_13_1_2_9_1_1186 14 41 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 230 (accept_3_2 13 41 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 230 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 41 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 230 (accept_3_2 10 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 41 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 230 (accept_3_2 7 41 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 230 (Polychromatic418967fa.accept_13_6_2_9_1_1188 6 41 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 230
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 5 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 230 (accept_3_2 4 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 230 (Polychromatic418967fa.accept_15_2_11_5_1_1266 2 41 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 230 (accept_3_2 1 41 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 230))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 230 (allA_of_3_0 40 40 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 230 (allA_succ_of_accept 38 39 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 230 (accept_3_2 37 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 230 (Polychromatic418967fa.accept_20_16_19_10_1_12352 36 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 230 (accept_3_2 34 39 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 230
  (Polychromatic418967fa.accept_19_13_1_2_1_11154 32 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 230 (accept_3_2 31 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 230 (accept_3_2 28 39 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 230 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 39 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 230 (accept_3_2 25 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 230 (accept_3_2 22 39 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 230 (accept_3_2 19 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 230 (accept_3_2 16 39 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 39 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 230
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 14 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 230 (accept_3_2 13 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 230 (accept_3_2 10 39 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 230 (accept_3_2 7 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  230 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 39 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 230 (accept_3_2 4 39 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 39 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  39 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 230 (accept_3_2 1 39 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 230))))))))))))))))))))))))))))))))))))))) (allB_succ 38 230
  (allA_succ_of_accept 37 38 230 (accept_3_2 37 38 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  230 2 18 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  35 38 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 38 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 230 2 17 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 38 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 230 2 16 19 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 230 (accept_3_2 31 38 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 230 2 15 19 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 230
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 29 38 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 230 2 14 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 38 230 (Polychromatic418967fa.accept_15_12_8_5_1_5048 27 38 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 230 2 13 19 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 230 (accept_3_2 25 38 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 230 2 12 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 38
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 230 2 11 19 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 38 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 230 2 10 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 38 230 (accept_3_2 19 38 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 38 230 2 9 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 38 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 38 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 230 2 8 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 15
  38 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 230 2 7 19 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 230 (accept_3_2 13
  38 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 230 2 6 19 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 38 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 38 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 38 230 2 5 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 38 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 38 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 230 2 4 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 230 (accept_3_2 7 38 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 38 230 2 3 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 38 230 (Polychromatic418967fa.accept_20_5_18_10_1_3565 5 38 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 230 2 2 19 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 38
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 230 2 1 19 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 230 (accept_3_2 1 38
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 230)))))))))))))))))))))))))))))))))))))) (allB_succ 37 230
  (allA_of_3_0 37 37 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 230 (allA_succ_of_accept 35 36 230
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 35 36 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 230 2 17 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 36 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 36 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 230 2 16 18 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 230 (accept_3_2 31 36 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 230 2 15 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 230 (Polychromatic418967fa.accept_11_7_3_10_1_1461
  29 36 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 230 2 14 18 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 230
  (Polychromatic418967fa.accept_13_1_10_9_1_215 27 36 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 230 2 13 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 36 230 (accept_3_2 25 36 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 230 2 12 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 36 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 36 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 230 2 11 18 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 230
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 21 36 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 36 230 2 10 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 36 230 (accept_3_2 19 36 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 230 2 9 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 230 (Polychromatic418967fa.accept_25_17_11_5_1_4675 17 36 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 230 2 8 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 230 (Polychromatic418967fa.accept_19_15_17_2_1_4097
  15 36 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 230 2 7 18 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 230 (accept_3_2 13
  36 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 230 2 6 18 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 230
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 36 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 36 230 2 5 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 36 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 36 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 230 2 4 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 230 (accept_3_2 7 36 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 36 230 2 3 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 36 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 36 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 230 2 2 18 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 230 (Polychromatic418967fa.accept_15_3_6_5_1_2079 3
  36 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 230 2 1 18 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 230 (accept_3_2 1 36
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 230)))))))))))))))))))))))))))))))))))) (allB_succ 35 230
  (allA_succ_of_accept 34 35 230 (accept_3_2 34 35 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  35 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 35 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 35 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 35 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 230 (accept_3_2 31 35 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 35 230 5 6 7 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 35 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 230 (accept_3_2 28 35 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 27
  35 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 230
  (Polychromatic418967fa.accept_19_7_16_2_1_6953 26 35 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 35 230 5 5 7 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 35 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 230 (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 35
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 230 (accept_3_2 22 35 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  35 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 35 230 5 4 7 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 35 230 (accept_3_2 19
  35 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 230
  (Polychromatic418967fa.accept_16_2_3_6_1_3372 18 35 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 230 (accept_3_2 16 35 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 35 230 5 3 7 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 35 230 (Polychromatic418967fa.accept_19_14_16_2_1_6952 14 35 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 230 (accept_3_2 13 35 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 35 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 35 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 35 230 5 2 7 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 35 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 35 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 230 (accept_3_2 7 35 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 6
  35 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 35 230 5 1 7 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 35 230 (accept_3_2 4 35
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 230 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 35 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 35 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 230 (accept_3_2 1 35 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  230))))))))))))))))))))))))))))))))))) (allB_succ 34 230 (allA_of_3_0 34 34 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 230 (allA_succ_of_accept 32 33 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 33 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 230 (accept_3_2 31 33 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 30
  33 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 230 (accept_3_2 28 33 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 33 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 230 (accept_3_2 25 33 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 230 (Polychromatic418967fa.accept_13_11_7_9_1_612 24 33 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 230 (accept_3_2 22 33 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 33 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 33 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 230 (accept_3_2 19 33 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 33 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 230 (accept_3_2 16 33 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 230 (Polychromatic418967fa.accept_22_14_11_10_1_5824 14 33 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 230 (accept_3_2 13 33 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 33 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 230 (accept_3_2 10 33 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  33 230 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 33 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 33 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 33 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 230 (accept_3_2 7 33 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 33 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 230 (accept_3_2 4 33 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 33 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 230 (accept_3_2 1 33 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 230))))))))))))))))))))))))))))))))) (allB_succ 32 230 (allA_succ_of_accept 31 32 230
  (accept_3_2 31 32 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 230 2 15 16 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 230
  (Polychromatic418967fa.accept_12_5_8_2_1_309 29 32 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 230 2 14 16 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 32 230 (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 32 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 230 2 13 16 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 230 (accept_3_2 25 32 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 230 2 12 16 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 23
  32 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 230 2 11 16 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 230
  (Polychromatic418967fa.accept_24_21_8_14_1_13728 21 32 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 32 230 2 10 16 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 32 230 (accept_3_2 19 32 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 32 230 2 9 16 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 32 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 32 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 32 230 2 8 16 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 32 230 (Polychromatic418967fa.accept_13_2_6_9_1_2636
  15 32 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 230 2 7 16 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 230 (accept_3_2 13
  32 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 230 2 6 16 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 32 230
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 32 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 32 230 2 5 16 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 32 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 32 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 230 2 4 16 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 230 (accept_3_2 7 32 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 32 230 2 3 16 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 32 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 32 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 32 230 2 2 16 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 32 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 32
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 230 2 1 16 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 230 (accept_3_2 1 32
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 230)))))))))))))))))))))))))))))))) (allB_succ 31 230
  (allA_of_3_0 31 31 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 230 (allA_succ_of_accept 29 30 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 30 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 230 2 14 15 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 30 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 30 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 230 2 13 15 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 30 230 5 5 6 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 30 230 2 12 15 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 230
  (Polychromatic418967fa.accept_19_4_11_2_1_11111 23 30 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 30 230 2 11 15 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 30 230 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 30 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 230 10 2 3 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 230 (accept_3_2 19 30 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 230 2 9 15 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 30 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 230 2 8 15 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 230 5 3 6 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 230 2 7 15 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 230 (accept_3_2 13
  30 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 230 2 6 15 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 30 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 230 10 1 3 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 30 230 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 30 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 230 2 4 15 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 230 (accept_3_2 7 30 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 30 230 2 3 15 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 5 30 230 5 1 6 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 4 30 230 2 2 15 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 30 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 230 2 1 15 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 230 (accept_3_2 1 30 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 30 230)))))))))))))))))))))))))))))) (allB_succ 29 230 (allA_succ_of_accept 28 29 230
  (accept_3_2 28 29 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 29 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 230 (accept_3_2 25 29 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 29 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  29 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 230 (accept_3_2 22 29
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 230 (Polychromatic418967fa.accept_6_3_5_2_1_12
  21 29 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 29 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 230 (accept_3_2 19 29 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 230 (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 29 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 29 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 230 (accept_3_2 16 29 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 230
  (Polychromatic418967fa.accept_11_3_7_10_1_180 14 29 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 230 (accept_3_2 13 29 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 29 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 230 (accept_3_2 10 29 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 230 (accept_3_2 7 29 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  230 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 29 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 29 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 230 (accept_3_2 4 29 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  29 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 230 (accept_3_2 1 29 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 230))))))))))))))))))))))))))))) (allB_succ 28 230 (allA_of_3_0
  28 28 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 230 (allA_succ_of_accept 26 27 230
  (Polychromatic418967fa.accept_11_4_5_10_1_926 26 27 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 230 (accept_3_2 25 27 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 230 (Polychromatic418967fa.accept_13_11_1_9_1_1179 24 27 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 230 (accept_3_2 22 27 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 230
  (Polychromatic418967fa.accept_16_4_11_6_1_5591 20 27 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 230 (accept_3_2 19 27 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 27 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 230 (accept_3_2 16 27 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 230 (Polychromatic418967fa.accept_11_4_5_10_1_926 15 27 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 230
  (Polychromatic418967fa.accept_19_14_8_2_1_6846 14 27 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 230 (accept_3_2 13 27 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 230 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 27 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 230 (accept_3_2 10 27 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 230
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 8 27 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 230 (accept_3_2 7 27 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  230 (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 27 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 27 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 230 (accept_3_2 4 27 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 230 (Polychromatic418967fa.accept_16_3_11_6_1_4467 3 27 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 230
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 2 27 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 230 (accept_3_2 1 27 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27
  230))))))))))))))))))))))))))) (allB_succ 26 230 (allA_succ_of_accept 25 26 230 (accept_3_2 25 26 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26 230 2 12 13 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 26 230 (Polychromatic418967fa.accept_15_8_11_5_1_169
  23 26 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 26 230 2 11 13 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 26 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 26 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 26 230 2 10 13 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 26 230 (accept_3_2 19 26 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 26 230 2 9 13 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 26 230 (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 26 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 230 2 8 13 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 15
  26 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 26 230 2 7 13 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 26 230 (accept_3_2 13
  26 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 230 2 6 13 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 26 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 26 230 2 5 13 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 26 230 (Polychromatic418967fa.accept_15_9_11_5_1_1283 9 26 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 230 2 4 13 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 230 (accept_3_2 7 26 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 26 230 2 3 13 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 26 230 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 26 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 230 2 2 13 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 26
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 230 2 1 13 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 230 (accept_3_2 1 26
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 230)))))))))))))))))))))))))) (allB_succ 25 230 (allA_of_3_0
  25 25 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 24 230 (allA_succ_of_accept 23 24 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 24 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 24 230 2 11 12 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 24 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 24 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 24 230 2 10 12 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 230 (accept_3_2 19 24 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 230 2 9 12 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 17
  24 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 230 2 8 12 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 230
  (Polychromatic418967fa.accept_13_2_11_9_1_591 15 24 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 24 230 2 7 12 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 230 (accept_3_2 13 24 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24
  230 2 6 12 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  24 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 24 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 24 230 2 5 12 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 24 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 24 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 24 230 2 4 12 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 230 (accept_3_2 7 24 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 230 2 3 12 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 230 (Polychromatic418967fa.accept_17_5_7_9_1_5122 5 24 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 230 2 2 12 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 24 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 24 230 2 1 12 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 24 230 (accept_3_2 1 24 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24
  230)))))))))))))))))))))))) (allB_succ 23 230 (allA_succ_of_accept 22 23 230 (accept_3_2 22 23 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 230
  (Polychromatic418967fa.accept_11_9_1_10_1_920 20 23 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 230 (accept_3_2 19 23 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 23 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 23 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 230 (accept_3_2 16 23 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 23 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 230
  (Polychromatic418967fa.accept_13_1_10_9_1_215 14 23 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 230 (accept_3_2 13 23 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 230 (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 23 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 23 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 230 (accept_3_2 10 23 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 23 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 230 (accept_3_2 7 23 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  230 (Polychromatic418967fa.accept_13_6_10_9_1_4329 6 23 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 23 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 230 (accept_3_2 4 23 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 230
  (Polychromatic418967fa.accept_11_2_1_10_1_196 2 23 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 230 (accept_3_2 1 23 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  230))))))))))))))))))))))) (allB_succ 22 230 (allA_of_3_0 22 22 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 21 230 (allA_succ_of_accept 20 21 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 21 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 230 (accept_3_2 19 21 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 21 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 230 (accept_3_2 16 21 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 21 230 (Polychromatic418967fa.accept_13_1_8_9_1_1154 14 21 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 230 (accept_3_2 13 21 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 230 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 21 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 230 (accept_3_2 10 21 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 230 (Polychromatic418967fa.accept_18_9_3_14_1_3361 9 21 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 21 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 230 (accept_3_2 7 21 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 21 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 230 (accept_3_2 4 21 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 21 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 230 (accept_3_2 1 21 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 21 230))))))))))))))))))))) (allB_succ 20 230 (allA_succ_of_accept 19 20 230 (accept_3_2 19 20
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 230 2 9 10 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 20 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 230 2 8 10 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 20 230 5 3 4 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 20 230 2 7 10 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 20 230 (accept_3_2 13 20 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20
  230 2 6 10 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  20 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 20 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 20 230 10 1 2 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 20 230 (Polychromatic418967fa.accept_19_9_1_2_1_6839 9 20 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 230 2 4 10 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 230 (accept_3_2 7 20 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 230 2 3 10 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 5 20 230 5 1 4 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 4 20 230 2 2 10 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 20 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 20 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 230 2 1 10 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 230 (accept_3_2 1 20 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 20 230)))))))))))))))))))) (allB_succ 19 230 (allA_of_3_0 19 19 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 18 230 (allA_succ_of_accept 17 18 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 18 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 18 230 2 8 9 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 18 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 15 18 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 18 230 2 7 9 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 18 230 (accept_3_2 13 18 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 18 230 2 6 9 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 18 230 (Polychromatic418967fa.accept_16_11_2_6_1_1435 11 18 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 230 2 5 9 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 18 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 18
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 230 2 4 9 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 230 (accept_3_2 7 18
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 230 2 3 9 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 18 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 18 230 2 2 9 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 18 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 18 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 18 230 2 1 9 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 230 (accept_3_2 1 18 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 18 230)))))))))))))))))) (allB_succ 17 230 (allA_succ_of_accept 16 17 230 (accept_3_2 16 17 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  17 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 230
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 14 17 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 230 (accept_3_2 13 17 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 17 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 230 (accept_3_2 10 17 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 17 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 230 (accept_3_2 7 17 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  230 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 17 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 230 (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 17 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 230 (accept_3_2 4 17 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 17
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 230 (accept_3_2 1 17 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 230))))))))))))))))) (allB_succ 16 230 (allA_of_3_0 16 16 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 230 (allA_succ_of_accept 14 15 230
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 14 15 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 230 (accept_3_2 13 15 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 15 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15 230 5 2 3 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 15 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 15 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 230 (accept_3_2 7 15 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  230 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 15 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 15 230 5 1 3 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 15 230 (accept_3_2 4 15 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15
  230 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 15 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 15 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 15 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 230 (accept_3_2 1 15 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 15 230))))))))))))))) (allB_succ 14 230 (allA_succ_of_accept 13 14 230 (accept_3_2 13 14 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 230 2 6 7 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 230 (Polychromatic418967fa.accept_13_11_1_9_1_1179
  11 14 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 230 2 5 7 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 230
  (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 14 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 14 230 2 4 7 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 14 230 (accept_3_2 7 14 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 14 230
  2 3 7 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14
  230 (Polychromatic418967fa.accept_13_5_1_9_1_618 5 14 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 14 230 2 2 7 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 14 230 (Polychromatic418967fa.accept_25_3_14_5_1_13727 3 14 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 230 2 1 7 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 230 (accept_3_2 1 14 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 230)))))))))))))) (allB_succ 13 230 (allA_of_3_0 13 13 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 230 (allA_succ_of_accept 11 12 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 12 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 230 2 5 6 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 230
  (Polychromatic418967fa.accept_11_9_1_10_1_920 9 12 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 230 2 4 6 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 230 (accept_3_2 7 12 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 230
  2 3 6 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12
  230 (Polychromatic418967fa.accept_17_5_12_9_1_10091 5 12 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 12 230 2 2 6 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 12 230 (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 12 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 230 2 1 6 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 230 (accept_3_2 1 12 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 12 230)))))))))))) (allB_succ 11 230 (allA_succ_of_accept 10 11 230 (accept_3_2 10 11
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  11 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 11 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 230 (accept_3_2 7 11 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  230 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 11 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 230 (accept_3_2 4 11 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  11 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 230 (accept_3_2 1 11 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 230))))))))))) (allB_succ 10 230 (allA_of_3_0 10 10 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 9 230 (allA_succ_of_accept 8 9 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 9 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 230 (accept_3_2 7 9 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 230
  (Polychromatic418967fa.accept_12_6_9_2_1_311 6 9 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 230 (accept_3_2 4 9 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 9 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 230 (Polychromatic418967fa.accept_16_2_9_6_1_4441 2
  9 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 230 (accept_3_2 1 9 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 230))))))))) (allB_succ 8 230 (allA_succ_of_accept 7 8 230
  (accept_3_2 7 8 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 230 2 3 4 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 8 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 8 230 2 2 4 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 8 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 8 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 230 2 1 4 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 230 (accept_3_2 1 8 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 230)))))))) (allB_succ 7 230 (allA_of_3_0 7 7 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 6 230 (allA_succ_of_accept 5 6 230 (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 6 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 230 2 2 3 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 6 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 230 2 1 3 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 230 (accept_3_2 1 6 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 230))))))
  (allB_succ 5 230 (allA_succ_of_accept 4 5 230 (accept_3_2 4 5 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 5 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 230 (Polychromatic418967fa.accept_13_2_5_9_1_610 2 5 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 230 (accept_3_2 1 5 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 230))))) (allB_succ 4 230 (allA_of_3_0 4 4 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 230 (allA_succ_of_accept 2 3 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 3 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 230 (accept_3_2 1 3 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 230))) (allB_succ 2 230 (allA_succ_of_accept 1 2 230 (accept_3_2 1 2 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 230)) (allB_two
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


