-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch243_Segment001
-- name    : Polychromatic418967fa_Branch243_Segment001
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:42:13.887563+00:00
-- url     : https://prove2.me/theorems/100a6149-8d36-4fa6-8245-051985183898
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch243_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_243_segment_001 : allB 143 243 :=
  allB_succ' 102 142 243 (Eq.refl Bool.true) (allA_succ_of_accept 101 142 243 (accept_3_5 101 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 142 243 (Polychromatic418967fa.accept_15_10_7_3_1_1939 100
  142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 142 243
  (Polychromatic418967fa.accept_13_8_12_9_1_1168 99 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 142 243 (accept_3_5 98 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 142 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 142 243 (Polychromatic418967fa.accept_17_11_6_5_1_3662 96 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 142 243 (accept_3_5 95 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 142 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 94 142 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 142 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 142 243 (accept_3_5 92 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 142 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 142 243 (Polychromatic418967fa.accept_11_2_10_1_1_1017 90 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 142 243 (accept_3_5 89 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 142 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 88 142 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 142 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 87 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 142 243 (accept_3_5 86 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 142 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 142 243 (Polychromatic418967fa.accept_18_12_16_9_1_4198 84 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 142 243 (accept_3_5 83 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 142 243 (Polychromatic418967fa.accept_19_6_9_15_1_3694 82 142
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 142 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 142 243 (accept_3_5 80 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 142 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 142 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313 78 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 142 243 (accept_3_5 77 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 142 243 (Polychromatic418967fa.accept_25_1_17_18_1_14683 76
  142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 142 243
  (Polychromatic418967fa.accept_10_5_2_3_1_239 75 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 142 243 (accept_3_5 74 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 142 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 142 243 (Polychromatic418967fa.accept_15_12_7_3_1_1940 72 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 142 243 (accept_3_5 71 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 142 243 (Polychromatic418967fa.accept_15_10_7_3_1_1939 70 142
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 142 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 142 243 (accept_3_5 68 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 142 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 142 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 142 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 142 243 (accept_3_5 65 142 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 142 243 (Polychromatic418967fa.accept_11_9_10_1_1_581 64 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 142 243
  (Polychromatic418967fa.accept_14_7_2_5_1_4528 63 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 142 243 (accept_3_5 62 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 142 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 142 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 142 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 142 243 (accept_3_5 59 142 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 142 243 (Polychromatic418967fa.accept_20_18_2_3_1_3169 58 142 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 142 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 142 243 (accept_3_5 56 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 142 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 142 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 142 243 (accept_3_5 53 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 142 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 142 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 142 243
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 51 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 142 243 (accept_3_5 50 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 142 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 142 243 (Polychromatic418967fa.accept_18_12_16_9_1_4198 48 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 142 243 (accept_3_5 47 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 142 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 142 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 142 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 142 243 (accept_3_5 44 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 142 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 142 243 (Polychromatic418967fa.accept_11_9_10_1_1_581 42 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 142 243 (accept_3_5 41 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 142 243 (Polychromatic418967fa.accept_15_10_7_3_1_1939 40 142
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 142 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 142 243 (accept_3_5 38 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 142 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 142 243 (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 142 243 (accept_3_5 35 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 142 243 (Polychromatic418967fa.accept_13_8_12_9_1_1168 34 142
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 142 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 142 243 (accept_3_5 32 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 142 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 142 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 142 243 (accept_3_5 29 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 142 243 (Polychromatic418967fa.accept_17_11_6_5_1_3662 28 142
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 142 243
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 27 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 142 243 (accept_3_5 26 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 142 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 142 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 142 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 142 243 (accept_3_5 23 142 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 142 243 (Polychromatic418967fa.accept_19_3_9_15_1_9240 22 142 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 142 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 142 243 (accept_3_5 20 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 142 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 142 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 142 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 142 243 (accept_3_5 17 142 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 142 243 (Polychromatic418967fa.accept_13_3_12_9_1_1193 16 142 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 142 243
  (Polychromatic418967fa.accept_10_5_2_3_1_239 15 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 142 243 (accept_3_5 14 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 142 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 142 243 (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 142 243 (accept_3_5 11 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 142 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 142 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 142 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 142 243 (accept_3_5 8 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  142 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 142 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 142 243 (accept_3_5 5 142 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 142 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 142 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 142 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 142 243 (accept_3_5 2 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  142 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 142 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 142
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 141 243 (Eq.refl Bool.true) (allA_succ_of_gcd 102 141 243 3 34 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 141 243 (Polychromatic418967fa.accept_7_3_1_5_1_44
  101 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 141 243
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 100 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 99 141 243 3 33 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 98 141 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 141 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 141 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 97 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 141 243 3 32 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 141 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 95 141 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 141 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 94
  141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 141 243 3 31 47 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 141 243
  (Polychromatic418967fa.accept_10_2_1_3_1_233 92 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 141 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 91 141 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 141 243 3 30 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 141 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 89
  141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 141 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 88 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 141 243 3 29 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 141 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 141 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 243 (Polychromatic418967fa.accept_12_1_9_3_1_370
  85 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 141 243 3 28 47 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 141 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 83 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 141 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 141 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 141 243 3 27 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 141 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 80
  141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 243
  (Polychromatic418967fa.accept_12_7_9_3_1_767 79 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 141 243 3 26 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 141 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 77 141 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 141 243 (Polychromatic418967fa.accept_7_6_1_5_1_322
  76 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 141 243 3 25 47 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 141 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 141 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 141 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 141 243 3 24 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 141 243 (Polychromatic418967fa.accept_12_11_9_3_1_792
  71 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 141 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 70 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 141 243 3 23 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 141 243 (Polychromatic418967fa.accept_10_8_1_3_1_1374 68 141 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 67 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 141 243 3 22 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 141 243 (Polychromatic418967fa.accept_11_10_9_1_1_2186 65 141 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 141 243
  (Polychromatic418967fa.accept_18_10_15_9_1_1054 64 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 141 243 3 21 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 141 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 141 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 61 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 141 243 3 20 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 141 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 141 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 58
  141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 141 243 3 19 47 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 141 243
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 56 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 141 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 141 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 141 243 3 18 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 141 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 53
  141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 52 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 141 243 3 17 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 141 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 141 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 243 (Polychromatic418967fa.accept_12_1_9_3_1_370
  49 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 141 243 3 16 47 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 141 243
  (Polychromatic418967fa.accept_12_11_9_3_1_792 47 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 141 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 141 243 3 15 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 141 243 (Polychromatic418967fa.accept_20_4_1_3_1_14682
  44 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 243
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 43 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 141 243 3 14 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 141 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 141 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 243
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 40 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 141 243 3 13 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 141 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 141 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 243 (Polychromatic418967fa.accept_12_1_9_3_1_370
  37 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 141 243 3 12 47 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 141 243
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 141 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 141 243 3 11 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 141 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 32
  141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 141 243 3 10 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 141 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 141 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 243 (Polychromatic418967fa.accept_10_8_1_3_1_1374
  28 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 141 243 3 9 47 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 141 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 141 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 141 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 141 243 3 8 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 141 243 (Polychromatic418967fa.accept_12_11_9_3_1_792
  23 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 141 243 3 7 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 141 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 141 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 141
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 141 243 3 6 47 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 141 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 243 (Polychromatic418967fa.accept_15_1_6_3_1_2827 16 141 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 141 243 3 5 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 141 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 141 243 3 4 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 141 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 141 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 141 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 141 243 3 3 47 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 141 243
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 141 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 141 243 3 2 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 141 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 141 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 4 141 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 141 243 3 1 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 141 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 141 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 140 243 (Eq.refl Bool.true) (allA_succ_of_accept 103 140 243 (accept_3_4 103 140 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 140 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 102 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 140 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 101 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 140 243 (accept_3_4 100 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 140 243 (Polychromatic418967fa.accept_15_9_5_3_1_554 99 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 140 243 (Polychromatic418967fa.accept_15_8_5_3_1_1990 98 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 140 243 (accept_3_4 97 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 140 243 (Polychromatic418967fa.accept_15_6_5_3_1_1988 96 140
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 140 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 140 243 (accept_3_4 94 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 140 243 (Polychromatic418967fa.accept_18_3_14_9_1_4264 93 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 140 243 (Polychromatic418967fa.accept_11_4_8_1_1_1047 92 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 140 243 (accept_3_4 91 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 140 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 90 140 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 140 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 89 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 140 243 (accept_3_4 88 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 140 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 87 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 140 243 (Polychromatic418967fa.accept_17_1_4_5_1_3501 86 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 140 243 (accept_3_4 85 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 140 243 (Polychromatic418967fa.accept_13_6_10_9_1_4329 84 140
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 140 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 140 243 (accept_3_4 82 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 140 243 (Polychromatic418967fa.accept_11_4_8_1_1_1047 81 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 140 243 (Polychromatic418967fa.accept_22_14_8_1_1_14681 80 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 140 243 (accept_3_4 79 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 140 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 78 140 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 140 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 140 243 (accept_3_4 76 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 140 243 (Polychromatic418967fa.accept_18_3_14_9_1_4264 75 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 140 243 (Polychromatic418967fa.accept_16_10_12_3_1_4252 74 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 140 243 (accept_3_4 73 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 140 243 (Polychromatic418967fa.accept_16_8_12_3_1_4194 72 140
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 140 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 140 243 (accept_3_4 70 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 140 243 (Polychromatic418967fa.accept_15_9_5_3_1_554 69 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 140 243 (Polychromatic418967fa.accept_15_8_5_3_1_1990 68 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 140 243 (accept_3_4 67 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 140 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 140 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 140 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 140 243 (accept_3_4 64 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 140 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 140 243 (Polychromatic418967fa.accept_15_2_5_3_1_552 62 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 140 243 (accept_3_4 61 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 140 243 (Polychromatic418967fa.accept_18_6_14_9_1_3039 60 140
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 140 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 140 243 (accept_3_4 58 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 140 243 (Polychromatic418967fa.accept_16_9_12_3_1_3138 57 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 140 243 (Polychromatic418967fa.accept_16_8_12_3_1_4194 56 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 140 243 (accept_3_4 55 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 140 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 140 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 140 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 140 243 (accept_3_4 52 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 140 243 (Polychromatic418967fa.accept_13_12_10_9_1_1166 51 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 140 243 (Polychromatic418967fa.accept_17_16_4_5_1_3626 50 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 140 243 (accept_3_4 49 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 140 243 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 140
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 140 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 140 243 (accept_3_4 46 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 140 243 (Polychromatic418967fa.accept_13_6_10_9_1_4329 45 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 140 243 (Polychromatic418967fa.accept_21_2_14_12_1_2713 44 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 140 243 (accept_3_4 43 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 140 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 140 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 140 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 140 243 (accept_3_4 40 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 140 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 140 243 (Polychromatic418967fa.accept_13_12_10_9_1_1166 38 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 140 243 (accept_3_4 37 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 140 243 (Polychromatic418967fa.accept_15_6_5_3_1_1988 36 140
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 140 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 140 243 (accept_3_4 34 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 140 243 (Polychromatic418967fa.accept_17_16_4_5_1_3626 33 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 140 243 (Polychromatic418967fa.accept_13_6_10_9_1_4329 32 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 140 243 (accept_3_4 31 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 140 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 140 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 140 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 140 243 (accept_3_4 28 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 140 243 (Polychromatic418967fa.accept_13_1_10_9_1_215 27 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 140 243 (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 140 243 (accept_3_4 25 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 140 243 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 140
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 140 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 140 243 (accept_3_4 22 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 140 243 (Polychromatic418967fa.accept_15_6_5_3_1_1988 21 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 140 243 (Polychromatic418967fa.accept_16_4_12_3_1_2180 20 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 140 243 (accept_3_4 19 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 140 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 140 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 140 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 140 243 (accept_3_4 16 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 140 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 140 243 (Polychromatic418967fa.accept_13_1_10_9_1_215 14 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 140 243 (accept_3_4 13 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 140 243 (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 140
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 140 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 140 243 (accept_3_4 10 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  140 243 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 140 243 (Polychromatic418967fa.accept_15_8_5_3_1_1990 8 140 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 140 243 (accept_3_4 7 140 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 140 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 140 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 140 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 140 243 (accept_3_4 4 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  140 243 (Polychromatic418967fa.accept_18_3_14_9_1_4264 3 140 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 140 243 (Polychromatic418967fa.accept_15_2_5_3_1_552 2 140 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 140 243 (accept_3_4 1 140 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 140
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 139 243 (Eq.refl Bool.true) (allA_succ_of_accept 104 139 243 (accept_3_5 104 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 139 243 (Polychromatic418967fa.accept_16_7_11_3_1_1330 103
  139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 139 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 102 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 139 243 (accept_3_5 101 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 139 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 139 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 99 139 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 139 243 (accept_3_5 98 139 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 139 243 (Polychromatic418967fa.accept_15_7_4_3_1_1930 97 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 139 243
  (Polychromatic418967fa.accept_10_6_9_3_1_935 96 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 139 243 (accept_3_5 95 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 139 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 139 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309 93 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 139 243 (accept_3_5 92 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 139 243 (Polychromatic418967fa.accept_15_1_4_3_1_1928 91 139
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 139 243
  (Polychromatic418967fa.accept_14_6_13_5_1_534 90 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 139 243 (accept_3_5 89 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 139 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 139 243 (Polychromatic418967fa.accept_16_7_11_3_1_1330 87 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 139 243 (accept_3_5 86 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 139 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 85 139 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 139 243
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 84 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 139 243 (accept_3_5 83 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 139 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 139 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 139 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 139 243 (accept_3_5 80 139 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 139 243 (Polychromatic418967fa.accept_16_15_11_3_1_2179 79 139 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 139 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 78 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 139 243 (accept_3_5 77 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 139 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 139 243 (Polychromatic418967fa.accept_18_3_13_9_1_4260 75 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 139 243 (accept_3_5 74 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 139 243 (Polychromatic418967fa.accept_19_16_6_15_1_2441 73 139
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 139 243
  (Polychromatic418967fa.accept_11_6_7_1_1_564 72 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 139 243 (accept_3_5 71 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 139 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 139 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309 69 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 139 243 (accept_3_5 68 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 139 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 139 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 139 243
  (Polychromatic418967fa.accept_10_6_9_3_1_935 66 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 139 243 (accept_3_5 65 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 139 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 139 243 (Polychromatic418967fa.accept_16_15_11_3_1_2179 63 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 139 243 (accept_3_5 62 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 139 243 (Polychromatic418967fa.accept_11_6_7_1_1_564 61 139
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 139 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 139 243 (accept_3_5 59 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 139 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 139 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 139 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 139 243 (accept_3_5 56 139 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 139 243 (Polychromatic418967fa.accept_16_7_11_3_1_1330 55 139 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 139 243
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 139 243 (accept_3_5 53 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 139 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 139 243 (Polychromatic418967fa.accept_19_13_6_15_1_9287 51 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 139 243 (accept_3_5 50 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 139 243 (Polychromatic418967fa.accept_19_11_6_15_1_14622 49
  139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 139 243
  (Polychromatic418967fa.accept_14_6_13_5_1_534 48 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 139 243 (accept_3_5 47 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 139 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 139 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 139 243 (accept_3_5 44 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 139 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 139 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 139 243
  (Polychromatic418967fa.accept_17_8_3_5_1_14680 42 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 139 243 (accept_3_5 41 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 139 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 139 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 139 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 139 243 (accept_3_5 38 139 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 139 243 (Polychromatic418967fa.accept_15_7_4_3_1_1930 37 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 139 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 139 243 (accept_3_5 35 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 139 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 139 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 243 (accept_3_5 32 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 139 243 (Polychromatic418967fa.accept_15_1_4_3_1_1928 31 139
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 243
  (Polychromatic418967fa.accept_16_14_11_3_1_4249 30 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 139 243 (accept_3_5 29 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 139 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 139 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 243 (Polychromatic418967fa.accept_29_27_23_11_1_14679 27
  139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 243 (accept_3_5 26
  139 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 139 243 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 139 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 243 (accept_3_5 23 139 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 139 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 139 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  21 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 243 (accept_3_5 20
  139 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 243
  (Polychromatic418967fa.accept_17_2_3_5_1_763 19 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 139 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 139 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 243 (accept_3_5 17 139 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 139 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 139 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 15
  139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 243 (accept_3_5 14
  139 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 243
  (Polychromatic418967fa.accept_19_13_6_15_1_9287 13 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 243 (Polychromatic418967fa.accept_19_12_6_15_1_5064 12 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 243 (accept_3_5 11 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 139 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 243
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 243 (accept_3_5 8 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 243 (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 243 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 139 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 243 (accept_3_5 5 139 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 139 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 243
  (Polychromatic418967fa.accept_18_3_13_9_1_4260 3 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 243 (accept_3_5 2 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 139 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 138 243 (Eq.refl Bool.true) (allA_succ_of_gcd 105 138 243 3 35 46 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 138 243
  (Polychromatic418967fa.accept_11_5_6_1_1_988 104 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 138 243 (Polychromatic418967fa.accept_13_12_8_9_1_1833 103 138 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 138 243 3 34 46 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 138 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 138 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 100 138 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 138 243 3 33 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 138 243 (Polychromatic418967fa.accept_12_2_6_3_1_331
  98 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 138 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 97 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 138 243 3 32 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 138 243 (Polychromatic418967fa.accept_10_5_8_3_1_229 95 138 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 138 243 (Polychromatic418967fa.accept_12_10_6_3_1_786
  94 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 138 243 3 31 46 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 138 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 92 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 138 243 (Polychromatic418967fa.accept_10_1_8_3_1_947 91 138 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 138 243 3 30 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 138 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 89
  138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 138 243
  (Polychromatic418967fa.accept_12_4_6_3_1_332 88 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 138 243 3 29 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 138 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 86 138 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 138 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 85
  138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 138 243 3 28 46 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 138 243
  (Polychromatic418967fa.accept_18_11_12_9_1_992 83 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 138 243 (Polychromatic418967fa.accept_11_5_6_1_1_988 82 138 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 138 243 3 27 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 138 243 (Polychromatic418967fa.accept_12_8_6_3_1_366
  80 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 138 243
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 79 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 138 243 3 26 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 138 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 138 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 138 243 (Polychromatic418967fa.accept_10_6_8_3_1_930
  76 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 138 243 3 25 46 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 138 243
  (Polychromatic418967fa.accept_12_2_6_3_1_331 74 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 138 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 138 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 138 243 3 24 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 138 243 (Polychromatic418967fa.accept_10_1_8_3_1_947
  71 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 138 243
  (Polychromatic418967fa.accept_12_10_6_3_1_786 70 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 138 243 3 23 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 138 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 68 138 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 138 243
  (Polychromatic418967fa.accept_17_16_2_5_1_6031 67 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 243 3 22 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 138 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 138 243 (Polychromatic418967fa.accept_12_4_6_3_1_332
  64 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 138 243 3 21 46 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 138 243
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 62 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 138 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 138 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 138 243 3 20 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 138 243 (Polychromatic418967fa.accept_13_7_8_9_1_1158
  59 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 138 243
  (Polychromatic418967fa.accept_12_10_6_3_1_786 58 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 138 243 3 19 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 138 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 56 138 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 138 243 (Polychromatic418967fa.accept_10_5_8_3_1_229
  55 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 138 243 3 18 46 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 138 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 138 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 52 138 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 138 243 3 17 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 138 243 (Polychromatic418967fa.accept_12_2_6_3_1_331
  50 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 138 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 243 3 16 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 243 (Polychromatic418967fa.accept_18_11_12_9_1_992 47 138 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 138 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 46 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 138 243 3 15 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 138 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 138 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 138 243 (Polychromatic418967fa.accept_13_4_8_9_1_1156
  43 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 138 243 3 14 46 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 138 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 138 243 (Polychromatic418967fa.accept_11_7_6_1_1_2182 40 138 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 138 243 3 13 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 138 243 (Polychromatic418967fa.accept_11_5_6_1_1_988
  38 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 243 3 12 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 243 (Polychromatic418967fa.accept_10_5_8_3_1_229 35 138 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 138 243 (Polychromatic418967fa.accept_12_10_6_3_1_786
  34 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 138 243 3 11 46 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 138 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 138 243 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 138 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 138 243 3 10 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 138 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 243
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 138 243 3 9 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 138 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 26 138 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 138 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 138 243 3 8 46 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 138 243
  (Polychromatic418967fa.accept_16_7_10_3_1_2210 23 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 138 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 138 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 138 243 3 7 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 138 243 (Polychromatic418967fa.accept_12_8_6_3_1_366
  20 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 243
  (Polychromatic418967fa.accept_24_19_18_3_1_11284 19 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 138 243 3 6 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 138 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 138 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 16 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 138 243 3 5 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 138 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 138 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 138 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 243 3 4 46 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 243
  (Polychromatic418967fa.accept_10_1_8_3_1_947 11 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 138 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 138 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 138 243 3 3 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 138 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 138 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 243
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 138 243 3 2 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 138 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 138 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 138 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 138 243 3 1 46 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 138 243
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 138 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 138 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 138 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 138
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 137 243 (Eq.refl Bool.true) (allA_succ_of_accept 106 137 243 (accept_3_4 106 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 137 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 105 137
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 137 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 104 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 137 243 (accept_3_4 103 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 137 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 137 243 (Polychromatic418967fa.accept_17_16_1_5_1_2600 101 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 137 243 (accept_3_4 100 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 137 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 99 137 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 137 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 137 243 (accept_3_4 97 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 137 243 (Polychromatic418967fa.accept_10_6_7_3_1_547 96 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 137 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 95 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 137 243 (accept_3_4 94 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 137 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 93 137 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 137 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 137 243 (accept_3_4 91 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 137 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 137 243 (Polychromatic418967fa.accept_13_11_7_9_1_612 89 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 137 243 (accept_3_4 88 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 137 243 (Polychromatic418967fa.accept_15_12_2_3_1_1146 87 137
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 137 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 137 243 (accept_3_4 85 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 137 243 (Polychromatic418967fa.accept_10_4_7_3_1_54 84 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 137 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 83 137 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 137 243 (accept_3_4 82 137 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 137 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 81 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 137 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 137 243 (accept_3_4 79 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 137 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 137 243 (Polychromatic418967fa.accept_19_1_4_15_1_2542 77 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 137 243 (accept_3_4 76 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 137 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 75 137
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 137 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 137 243 (accept_3_4 73 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 137 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 137 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 71 137 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 137 243 (accept_3_4 70 137 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 137 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 137 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 137 243 (accept_3_4 67 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 137 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 137 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 137 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 137 243 (accept_3_4 64 137 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 137 243 (Polychromatic418967fa.accept_13_11_7_9_1_612 63 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 137 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 137 243 (accept_3_4 61 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 137 243 (Polychromatic418967fa.accept_13_8_7_9_1_611 60 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 137 243 (Polychromatic418967fa.accept_15_14_2_3_1_1980 59 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 137 243 (accept_3_4 58 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 137 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 137 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 137 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 137 243 (accept_3_4 55 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 137 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 137 243 (Polychromatic418967fa.accept_22_9_5_1_1_2204 53 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 243 (accept_3_4 52 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 137 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 137 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 137 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 137 243 (accept_3_4 49 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 137 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 137 243 (Polychromatic418967fa.accept_13_8_7_9_1_611 47 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 243 (accept_3_4 46 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 137 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 137
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 137 243 (accept_3_4 43 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 137 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 137 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 243 (accept_3_4 40 137 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 243 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 137 243 (accept_3_4 37 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 137 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 35 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 243 (accept_3_4 34 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 137
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 243 (accept_3_4 31 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 137 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 243 (accept_3_4 28 137 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 243 (accept_3_4 25 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 243 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 137 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 243 (accept_3_4 22 137 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 243 (accept_3_4 19 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 243 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 243 (accept_3_4 16 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 137 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 243 (accept_3_4 13 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 243 (Polychromatic418967fa.accept_15_12_2_3_1_1146 12 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 243 (Polychromatic418967fa.accept_13_11_7_9_1_612 11 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 243 (accept_3_4 10 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 137 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 243 (accept_3_4 7 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 137 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 243 (accept_3_4 4 137 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 243 (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 137 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 243 (accept_3_4 1 137 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 136 243 (Eq.refl Bool.true) (allA_succ_of_accept 107 136 243 (accept_3_5 107 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 136 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 106 136
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 136 243
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 105 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 136 243 (accept_3_5 104 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 103 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 136 243 (Polychromatic418967fa.accept_12_6_4_3_1_361 102 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 136 243 (accept_3_5 101 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 136 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 100 136
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 136 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 99 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 136 243 (accept_3_5 98 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 97 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 136 243 (Polychromatic418967fa.accept_11_8_4_1_1_1000 96 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 136 243 (accept_3_5 95 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 136 243 (Polychromatic418967fa.accept_13_3_6_9_1_1150 94 136
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 136 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 93 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 136 243 (accept_3_5 92 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 136 243 (Polychromatic418967fa.accept_12_6_4_3_1_361 90 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 136 243 (accept_3_5 89 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 136 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 88 136
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 136 243
  (Polychromatic418967fa.accept_10_7_6_3_1_927 87 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 136 243 (accept_3_5 86 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 136 243 (Polychromatic418967fa.accept_16_4_8_3_1_4206 84 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 136 243 (accept_3_5 83 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 136 243 (Polychromatic418967fa.accept_13_4_6_9_1_3401 82 136
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 136 243
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 81 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 136 243 (accept_3_5 80 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 136 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 136 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 136 243 (accept_3_5 77 136 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 136 243 (Polychromatic418967fa.accept_16_12_8_3_1_4241 76 136 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 136 243
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 75 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 136 243 (accept_3_5 74 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 136 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 136 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 136 243 (accept_3_5 71 136 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 136 243 (Polychromatic418967fa.accept_25_20_11_18_1_12952 70 136 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 136 243
  (Polychromatic418967fa.accept_10_9_6_3_1_545 69 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 136 243 (accept_3_5 68 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 136 243 (Polychromatic418967fa.accept_12_6_4_3_1_361 66 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 136 243 (accept_3_5 65 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 136 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 136 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 136 243
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 136 243 (accept_3_5 62 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 136 243 (Polychromatic418967fa.accept_16_12_8_3_1_4241 60 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 136 243 (accept_3_5 59 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 136 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 136 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 136 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 136 243 (accept_3_5 56 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 136 243 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 136 243 (accept_3_5 53 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 136 243 (Polychromatic418967fa.accept_11_8_4_1_1_1000 52 136
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 136 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 136 243 (accept_3_5 50 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 136 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 136 243 (accept_3_5 47 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 136 243 (Polychromatic418967fa.accept_13_7_6_9_1_1831 46 136
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 136 243
  (Polychromatic418967fa.accept_16_13_8_3_1_5374 45 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 136 243 (accept_3_5 44 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 136 243 (Polychromatic418967fa.accept_12_6_4_3_1_361 42 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 136 243 (accept_3_5 41 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 136 243 (Polychromatic418967fa.accept_13_1_6_9_1_1197 40 136
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 136 243
  (Polychromatic418967fa.accept_10_9_6_3_1_545 39 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 136 243 (accept_3_5 38 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 136 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 136 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 136 243 (accept_3_5 35 136 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 136 243 (Polychromatic418967fa.accept_15_4_1_3_1_1922 34 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 136 243
  (Polychromatic418967fa.accept_13_7_6_9_1_1831 33 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 136 243 (accept_3_5 32 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 136 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 136 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 136 243 (accept_3_5 29 136 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 136 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 136 243
  (Polychromatic418967fa.accept_10_7_6_3_1_927 27 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 136 243 (accept_3_5 26 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 136 243 (Polychromatic418967fa.accept_21_3_10_12_1_10278 24 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 136 243 (accept_3_5 23 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 136 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 136 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 136 243
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 21 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 136 243 (accept_3_5 20 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 136 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 136 243 (accept_3_5 17 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 136 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 136 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 136 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 136 243 (accept_3_5 14 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 136 243 (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 136 243 (accept_3_5 11 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 136 243 (Polychromatic418967fa.accept_13_10_6_9_1_1152 10 136
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 136 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 136 243 (accept_3_5 8 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 136 243 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 136 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 136 243 (accept_3_5 5 136 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 136 243 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 136 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 136 243
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 3 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 136 243 (accept_3_5 2 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  136 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 136 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 136
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 135 243 (Eq.refl Bool.true) (allA_succ_of_gcd 108 135 243 27 4 5 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 135 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 107 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 135 243 (Polychromatic418967fa.accept_13_2_5_9_1_610 106 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 135 243 3 35 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 135 243
  (Polychromatic418967fa.accept_17_2_16_5_1_1584 104 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 135 243 (Polychromatic418967fa.accept_17_1_16_5_1_3670 103 135 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 135 243 3 34 45 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 135 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 101 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 135 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 100 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 135 243 9 11 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 135 243 (Polychromatic418967fa.accept_10_8_5_3_1_543
  98 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 135 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 97 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 135 243 3 32 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 135 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 95 135 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 135 243 (Polychromatic418967fa.accept_7_3_2_5_1_147
  94 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 135 243 3 31 45 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 135 243
  (Polychromatic418967fa.accept_8_4_7_3_1_144 92 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 135 243 (Polychromatic418967fa.accept_14_7_9_5_1_529 91 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 135 243 9 10 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 135 243 (Polychromatic418967fa.accept_16_9_7_3_1_614
  89 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 135 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 88 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 135 243 3 29 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 135 243 (Polychromatic418967fa.accept_17_1_16_5_1_3670 86 135 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 135 243
  (Polychromatic418967fa.accept_19_9_2_15_1_6432 85 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 135 243 3 28 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 135 243 (Polychromatic418967fa.accept_21_20_9_12_1_5549 83 135 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 135 243
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 82 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 135 243 27 3 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 135 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 80 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 135 243 (Polychromatic418967fa.accept_11_2_3_1_1_244 79 135
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 135 243 3 26 45 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 135 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 77 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 135 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 76 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 135 243 3 25 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 135 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 74
  135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 73 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 135 243 9 8 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 135 243 (Polychromatic418967fa.accept_21_8_9_12_1_7118 71 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 243 (Polychromatic418967fa.accept_17_2_16_5_1_1584 70 135
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 135 243 3 23 45 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 135 243
  (Polychromatic418967fa.accept_8_4_7_3_1_144 68 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 135 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 135 243 3 22 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 135 243 (Polychromatic418967fa.accept_19_8_2_15_1_2426
  65 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 135 243
  (Polychromatic418967fa.accept_21_1_9_12_1_2719 64 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 135 243 9 7 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 135 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408 62 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 243 (Polychromatic418967fa.accept_21_19_9_12_1_4071 61 135
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 135 243 3 20 45 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 135 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 59 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 135 243 (Polychromatic418967fa.accept_10_8_5_3_1_543 58 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 135 243 3 19 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 135 243 (Polychromatic418967fa.accept_13_4_5_9_1_1829
  56 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 243
  (Polychromatic418967fa.accept_13_3_5_9_1_5285 55 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 135 243 27 2 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 135 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 135 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 135 243 3 17 45 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 135 243
  (Polychromatic418967fa.accept_20_10_15_3_1_7387 50 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 135 243 (Polychromatic418967fa.accept_14_7_9_5_1_529 49 135 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 135 243 3 16 45 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 135 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 47 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 135 243 9 5 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 135 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 44
  135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 243
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 43 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 135 243 3 14 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 135 243 (Polychromatic418967fa.accept_13_2_5_9_1_610 41 135 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 243 (Polychromatic418967fa.accept_13_1_5_9_1_226
  40 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 135 243 3 13 45 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 135 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 135 243 9 4 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 135 243 (Polychromatic418967fa.accept_11_2_3_1_1_244
  35 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 243
  (Polychromatic418967fa.accept_21_13_9_12_1_4038 34 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 135 243 3 11 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 135 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 135 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 135 243 3 10 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 135 243 (Polychromatic418967fa.accept_13_3_5_9_1_5285 29 135 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 243
  (Polychromatic418967fa.accept_8_4_7_3_1_144 28 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 135 243 27 1 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 135 243 (Polychromatic418967fa.accept_16_10_7_3_1_6601 26 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 135 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 135 243 3 8 45 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 135 243
  (Polychromatic418967fa.accept_21_2_9_12_1_4040 23 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408 22 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 135 243 3 7 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 135 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 20
  135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 243
  (Polychromatic418967fa.accept_17_2_16_5_1_1584 19 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 135 243 9 2 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 135 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 243 (Polychromatic418967fa.accept_13_3_5_9_1_5285 16 135
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 243 3 5 45 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 243
  (Polychromatic418967fa.accept_13_1_5_9_1_226 14 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 243 (Polychromatic418967fa.accept_11_2_3_1_1_244 13 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 243 3 4 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 11
  135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 10 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 135 243 9 1 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 135 243 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 135 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 135 243 3 2 45 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 135 243
  (Polychromatic418967fa.accept_20_5_15_3_1_4516 5 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 135 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 135 243 3 1 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 135 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408 2 135 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 243
  (Polychromatic418967fa.accept_13_1_5_9_1_226 1 135 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 135
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 134 243 (Eq.refl Bool.true) (allA_succ_of_accept 109 134 243 (accept_3_4 109 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 134 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 108 134
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 134 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 107 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 134 243 (accept_3_4 106 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 134 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 134 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 104 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 134 243 (accept_3_4 103 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 134 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 102 134
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 134 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 134 243 (accept_3_4 100 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 134 243 (Polychromatic418967fa.accept_10_9_4_3_1_539 99 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 134 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 98 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 134 243 (accept_3_4 97 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 134 243 (Polychromatic418967fa.accept_13_5_4_9_1_601 96 134
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 134 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 134 243 (accept_3_4 94 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 134 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 134 243 (Polychromatic418967fa.accept_15_2_14_3_1_1916 92 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 134 243 (accept_3_4 91 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 134 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 90 134 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 134 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 134 243 (accept_3_4 88 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 134 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 134 243 (Polychromatic418967fa.accept_13_8_4_9_1_1145 86 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 134 243 (accept_3_4 85 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 134 243 (Polychromatic418967fa.accept_13_6_4_9_1_4326 84 134
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 134 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 134 243 (accept_3_4 82 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 134 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 134 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 80 134 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 134 243 (accept_3_4 79 134 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 134 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 78 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 134 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 134 243 (accept_3_4 76 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 134 243 (Polychromatic418967fa.accept_16_11_6_3_1_6564 75 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 134 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 74 134 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 134 243 (accept_3_4 73 134 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 134 243 (Polychromatic418967fa.accept_13_7_4_9_1_1865 72 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 134 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 134 243 (accept_3_4 70 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 134 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 134 243 (Polychromatic418967fa.accept_16_4_6_3_1_1311 68 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 134 243 (accept_3_4 67 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 134 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 134 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 134 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 134 243 (accept_3_4 64 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 134 243 (Polychromatic418967fa.accept_23_17_19_13_1_11426 63 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 62 134 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 62 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 134 243 (accept_3_4 61 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 134 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 134 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 134 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 134 243 (accept_3_4 58 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 134 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 134 243 (Polychromatic418967fa.accept_15_11_14_3_1_1965 56 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 134 243 (accept_3_4 55 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 134 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 134
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 134 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 134 243 (accept_3_4 52 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 134 243 (Polychromatic418967fa.accept_20_11_14_3_1_5975 51 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 134 243 (Polychromatic418967fa.accept_16_2_6_3_1_5396 50 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 134 243 (accept_3_4 49 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 134 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 134 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 134 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 134 243 (accept_3_4 46 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 134 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 134 243 (Polychromatic418967fa.accept_13_5_4_9_1_601 44 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 134 243 (accept_3_4 43 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 134 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 134
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 134 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 134 243 (accept_3_4 40 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 134 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 134 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 134 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 134 243 (accept_3_4 37 134 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 134 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 134 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 134 243 (accept_3_4 34 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 134 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 134 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 134 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 134 243 (accept_3_4 31 134 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 134 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 134 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 134 243 (accept_3_4 28 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 134 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 134 243 (Polychromatic418967fa.accept_15_11_14_3_1_1965 26 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 134 243 (accept_3_4 25 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 134 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 134 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 134 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 134 243 (accept_3_4 22 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 134 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 134 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 134 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 134 243 (accept_3_4 19 134 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 134 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 134 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 134 243 (accept_3_4 16 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 134 243 (Polychromatic418967fa.accept_21_15_8_12_1_8687 15 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 134 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 134 243 (accept_3_4 13 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 134 243 (Polychromatic418967fa.accept_22_12_2_1_1_14678 12 134
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 134 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 134 243 (accept_3_4 10 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  134 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 134 243 (Polychromatic418967fa.accept_13_8_4_9_1_1145 8 134 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 134 243 (accept_3_4 7 134 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 134 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 134 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 134 243 (accept_3_4 4 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  134 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 134 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 134 243 (Polychromatic418967fa.accept_15_2_14_3_1_1916 2 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 134 243 (accept_3_4 1 134 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 134
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 111 133 243 (Eq.refl Bool.true) (allA_succ_of_accept 110 133 243 (accept_3_5 110 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 133 243 (Polychromatic418967fa.accept_13_5_3_9_1_1189 109 133
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 133 243
  (Polychromatic418967fa.accept_20_8_13_3_1_9081 108 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 133 243 (accept_3_5 107 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 133 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 133 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 133 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 105 133
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 133 243 (accept_3_5 104 133
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 133 243
  (Polychromatic418967fa.accept_13_12_3_9_1_4341 103 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 133 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 133 243 (accept_3_5 101 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 133 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 133
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 133 243
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 99 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 133 243 (accept_3_5 98 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 133 243 (Polychromatic418967fa.accept_13_6_3_9_1_1827 97 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 133 243 (Polychromatic418967fa.accept_13_5_3_9_1_1189 96 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 133 243 (accept_3_5 95 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 133 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 133 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 133 243
  (Polychromatic418967fa.accept_12_9_1_3_1_350 93 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 133 243 (accept_3_5 92 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 133 243 (Polychromatic418967fa.accept_15_1_13_3_1_2002 91 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 133 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 133 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 133 243 (accept_3_5 89 133 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 133 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 133 243
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 87 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 133 243 (accept_3_5 86 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 133 243 (Polychromatic418967fa.accept_13_7_3_9_1_1142 85 133 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 133 243 (Polychromatic418967fa.accept_13_6_3_9_1_1827 84 133
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 133 243 (accept_3_5 83 133
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 133 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 82 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 133 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 81 133 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 133 243 (accept_3_5 80 133 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 133 243 (Polychromatic418967fa.accept_14_9_7_5_1_1105 79 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 133 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 133 243 (accept_3_5 77 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 133 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 133 243 (Polychromatic418967fa.accept_18_3_7_9_1_5486 75 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 133 243 (accept_3_5 74 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 133 243 (Polychromatic418967fa.accept_13_8_3_9_1_5269 73 133
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 133 243
  (Polychromatic418967fa.accept_13_7_3_9_1_1142 72 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 133 243 (accept_3_5 71 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 133 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 133 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 69 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 133 243 (accept_3_5 68 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 133 243 (Polychromatic418967fa.accept_13_2_3_9_1_2610 67 133
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 133 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 133 243 (accept_3_5 65 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 133 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 133 243 (Polychromatic418967fa.accept_25_13_8_18_1_14631 63 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 133 243 (accept_3_5 62 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 133 243 (Polychromatic418967fa.accept_15_1_13_3_1_2002 61 133
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 133 243
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 60 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 133 243 (accept_3_5 59 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 133 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 133 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 57 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 133 243 (accept_3_5 56 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 133 243 (Polychromatic418967fa.accept_15_10_13_3_1_4816 55 133
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 133 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 133 243 (accept_3_5 53 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 133 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 133 243 (Polychromatic418967fa.accept_13_12_3_9_1_4341 51 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 133 243 (accept_3_5 50 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 133 243 (Polychromatic418967fa.accept_31_18_9_26_1_14677 49
  133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 133 243
  (Polychromatic418967fa.accept_20_8_13_3_1_9081 48 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 133 243 (accept_3_5 47 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 133 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 133 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 133 243 (accept_3_5 44 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 133 243 (Polychromatic418967fa.accept_17_9_14_5_1_1555 43 133
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 133 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 133 243 (accept_3_5 41 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 133 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 133 243 (Polychromatic418967fa.accept_15_9_13_3_1_535 39 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 243 (accept_3_5 38 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 133 243 (Polychromatic418967fa.accept_14_9_7_5_1_1105 37 133
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 133 243
  (Polychromatic418967fa.accept_17_2_14_5_1_2575 36 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 133 243 (accept_3_5 35 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 133 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 133 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 243 (accept_3_5 32 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 133 243 (Polychromatic418967fa.accept_13_5_3_9_1_1189 31 133
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 133 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 133 243 (accept_3_5 29 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 133 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 133 243 (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 243 (accept_3_5 26 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 243 (Polychromatic418967fa.accept_13_12_3_9_1_4341 25 133
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 243
  (Polychromatic418967fa.accept_15_9_13_3_1_535 24 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 133 243 (accept_3_5 23 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 133 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 133 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 243 (accept_3_5 20 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 243 (Polychromatic418967fa.accept_13_6_3_9_1_1827 19 133
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 133 243 (accept_3_5 17 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 133 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 133 243 (Polychromatic418967fa.accept_13_2_3_9_1_2610 15 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 243 (accept_3_5 14 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 243 (Polychromatic418967fa.accept_25_13_8_18_1_14631 13
  133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 243
  (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 243 (accept_3_5 11 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 133 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 243 (accept_3_5 8 133 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 243 (Polychromatic418967fa.accept_13_7_3_9_1_1142 7 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 243 (accept_3_5 5 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 133 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 243 (Polychromatic418967fa.accept_18_3_7_9_1_5486 3 133 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 243 (accept_3_5 2 133 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 243 (Polychromatic418967fa.accept_15_1_13_3_1_2002 1 133 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 132 243 (Eq.refl Bool.true) (allA_succ_of_gcd 111 132 243 3 37 44 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 132 243
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 110 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 132 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 109 132 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 132 243 3 36 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 132 243 (Polychromatic418967fa.accept_13_3_2_9_1_1187
  107 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 132 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 106 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 132 243 3 35 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 132 243 (Polychromatic418967fa.accept_16_8_4_3_1_3146 104 132 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 132 243
  (Polychromatic418967fa.accept_8_7_4_3_1_156 103 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 132 243 3 34 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 132 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 101 132 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 132 243
  (Polychromatic418967fa.accept_17_15_13_5_1_9877 100 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 99 132 243 3 33 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 98 132 243 (Polychromatic418967fa.accept_13_7_2_9_1_1826 98 132 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 132 243
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 97 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 132 243 3 32 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 132 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 95 132 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 132 243 (Polychromatic418967fa.accept_13_3_2_9_1_1187
  94 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 132 243 3 31 44 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 132 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 92 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 132 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 91 132 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 132 243 3 30 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 132 243 (Polychromatic418967fa.accept_13_11_2_9_1_2640
  89 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 132 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 88 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 132 243 3 29 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 132 243 (Polychromatic418967fa.accept_16_6_4_3_1_2189 86 132 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 132 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 85 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 132 243 3 28 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 132 243 (Polychromatic418967fa.accept_13_5_2_9_1_1195 83 132 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 132 243
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 82 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 132 243 3 27 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 132 243 (Polychromatic418967fa.accept_18_8_6_9_1_5576 80 132 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 132 243
  (Polychromatic418967fa.accept_8_7_4_3_1_156 79 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 243 3 26 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 243 (Polychromatic418967fa.accept_15_2_12_3_1_1183 77 132 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 132 243
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 76 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 132 243 3 25 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 132 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 74 132 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 132 243
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 73 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 132 243 3 24 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 132 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 71 132 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 132 243
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 70 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 132 243 3 23 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 132 243 (Polychromatic418967fa.accept_13_3_2_9_1_1187 68 132 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 132 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 67 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 243 3 22 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 243 (Polychromatic418967fa.accept_10_5_2_3_1_239 65 132 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 132 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 64
  132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 132 243 3 21 44 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 132 243
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 62 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 132 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 61 132 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 132 243 3 20 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 132 243 (Polychromatic418967fa.accept_13_7_2_9_1_1826
  59 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 132 243
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 58 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 132 243 3 19 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 132 243 (Polychromatic418967fa.accept_16_8_4_3_1_3146 56 132 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 132 243
  (Polychromatic418967fa.accept_8_7_4_3_1_156 55 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 243 3 18 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 132 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 132 243
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 52 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 132 243 3 17 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 132 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 50 132 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 132 243 (Polychromatic418967fa.accept_16_1_4_3_1_3148
  49 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 132 243 3 16 44 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 132 243
  (Polychromatic418967fa.accept_8_7_4_3_1_156 47 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 132 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 132 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 132 243 3 15 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 132 243 (Polychromatic418967fa.accept_13_5_2_9_1_1195
  44 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 132 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 43 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 243 3 14 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 41 132 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 243
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 40 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 132 243 3 13 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 132 243 (Polychromatic418967fa.accept_15_8_12_3_1_1912 38 132 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 132 243
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 37 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 243 3 12 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 132 243 (Polychromatic418967fa.accept_10_5_2_3_1_239 35 132 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 243
  (Polychromatic418967fa.accept_23_11_17_13_1_13025 34 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 132 243 3 11 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 132 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 132 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 132 243
  (Polychromatic418967fa.accept_8_7_4_3_1_156 31 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 243 3 10 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 132 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 243
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 28 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 132 243 3 9 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 132 243 (Polychromatic418967fa.accept_17_9_13_5_1_3512 26 132 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 132 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 243 3 8 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 132 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 132 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 132 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 132 243 3 7 44 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 132 243
  (Polychromatic418967fa.accept_13_7_2_9_1_1826 20 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 132 243 (Polychromatic418967fa.accept_13_6_2_9_1_1188 19 132 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 243 3 6 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 243 (Polychromatic418967fa.accept_15_2_12_3_1_1183
  17 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 243
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 16 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 132 243 3 5 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 132 243 (Polychromatic418967fa.accept_13_1_2_9_1_1186 14 132 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 243 (Polychromatic418967fa.accept_14_13_6_5_1_1853 13 132
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 243 3 4 44 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 132 243 (Polychromatic418967fa.accept_17_10_13_5_1_3513 10 132 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 132 243 3 3 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 132 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 8
  132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 243
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 132 243 3 2 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 132 243 (Polychromatic418967fa.accept_10_5_2_3_1_239 5 132 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 132 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 132 243 3 1 44 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 132 243
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 2 132 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 132 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 132
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 131 243 (Eq.refl Bool.true) (allA_succ_of_accept 112 131 243 (accept_3_4 112 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 131 243 (Polychromatic418967fa.accept_15_6_11_3_1_1172 111
  131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 110 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 131 243 (accept_3_4 109 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 131 243 (Polychromatic418967fa.accept_10_8_1_3_1_1374 108 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 131 243 (Polychromatic418967fa.accept_19_12_17_15_1_6460 107 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 131 243 (accept_3_4 106 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 131 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 105 131
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 104 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 131 243 (accept_3_4 103 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 131 243 (Polychromatic418967fa.accept_10_2_1_3_1_233 102 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 131 243 (Polychromatic418967fa.accept_11_2_10_1_1_1017 101 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 131 243 (accept_3_4 100 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 131 243 (Polychromatic418967fa.accept_13_8_1_9_1_1178 99 131
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 98 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 131 243 (accept_3_4 97 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 131 243 (Polychromatic418967fa.accept_13_5_1_9_1_618 96 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 131 243 (Polychromatic418967fa.accept_17_10_12_5_1_6028 95 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 131 243 (accept_3_4 94 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 131 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 93 131
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 131 243 (accept_3_4 91 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 131 243 (Polychromatic418967fa.accept_11_2_10_1_1_1017 90 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 131 243 (Polychromatic418967fa.accept_13_11_1_9_1_1179 89 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 131 243 (accept_3_4 88 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 131 243 (Polychromatic418967fa.accept_18_15_5_9_1_5529 87 131
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 86 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 131 243 (accept_3_4 85 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 131 243 (Polychromatic418967fa.accept_13_6_1_9_1_619 84 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 131 243 (Polychromatic418967fa.accept_13_5_1_9_1_618 83 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 131 243 (accept_3_4 82 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 131 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 81 131
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 131 243 (accept_3_4 79 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 131 243 (Polychromatic418967fa.accept_10_8_1_3_1_1374 78 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 131 243 (Polychromatic418967fa.accept_17_9_12_5_1_219 77 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 131 243 (accept_3_4 76 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 131 243 (Polychromatic418967fa.accept_11_9_10_1_1_581 75 131
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 74 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 131 243 (accept_3_4 73 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 131 243 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 131 243 (Polychromatic418967fa.accept_13_6_1_9_1_619 71 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 131 243 (accept_3_4 70 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 131 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 69 131
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 131 243 (accept_3_4 67 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 131 243 (Polychromatic418967fa.accept_15_6_11_3_1_1172 66 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 131 243 (Polychromatic418967fa.accept_19_8_17_15_1_11952 65 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 243 (accept_3_4 64 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 131 243 (Polychromatic418967fa.accept_13_11_1_9_1_1179 63 131
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 131 243 (accept_3_4 61 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 131 243 (Polychromatic418967fa.accept_13_8_1_9_1_1178 60 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 131 243 (Polychromatic418967fa.accept_15_14_11_3_1_1957 59 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 243 (accept_3_4 58 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 131 243 (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 131
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 131 243 (accept_3_4 55 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 131 243 (Polychromatic418967fa.accept_13_2_1_9_1_1174 54 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 131 243 (Polychromatic418967fa.accept_11_9_10_1_1_581 53 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 243 (accept_3_4 52 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 131 243 (Polychromatic418967fa.accept_15_6_11_3_1_1172 51 131
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 131 243 (accept_3_4 49 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 131 243 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 131 243 (Polychromatic418967fa.accept_13_8_1_9_1_1178 47 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 243 (accept_3_4 46 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 131
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 243 (accept_3_4 43 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 243 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 243 (Polychromatic418967fa.accept_13_2_1_9_1_1174 41 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 243 (accept_3_4 40 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 243 (Polychromatic418967fa.accept_19_1_17_15_1_7897 39 131
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 243 (accept_3_4 37 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 243 (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 243 (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 243 (accept_3_4 34 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 131
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 243 (accept_3_4 31 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 243 (Polychromatic418967fa.accept_18_12_5_9_1_6896 30 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 243 (Polychromatic418967fa.accept_15_14_11_3_1_1957 29 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 243 (accept_3_4 28 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 243 (Polychromatic418967fa.accept_17_10_12_5_1_6028 27 131
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 243 (accept_3_4 25 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 243 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 243 (Polychromatic418967fa.accept_13_10_1_9_1_3380 23 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 243 (accept_3_4 22 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 131
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 243 (accept_3_4 19 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 243 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 243 (Polychromatic418967fa.accept_21_17_5_12_1_14676 17 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 243 (accept_3_4 16 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 243 (Polychromatic418967fa.accept_13_2_1_9_1_1174 15 131
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 131 243 (accept_3_4 13 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 131 243 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 131 243 (Polychromatic418967fa.accept_13_11_1_9_1_1179 11 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 243 (accept_3_4 10 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 243 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 131 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 243 (accept_3_4 7 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 243 (Polychromatic418967fa.accept_13_6_1_9_1_619 6 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 243 (Polychromatic418967fa.accept_13_5_1_9_1_618 5 131 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 243 (accept_3_4 4 131 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 243 (Polychromatic418967fa.accept_19_3_17_15_1_6459 3 131 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 243 (accept_3_4 1 131 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 114 130 243 (Eq.refl Bool.true) (allA_succ_of_accept 113 130 243 (accept_3_5 113 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 130 243 (Polychromatic418967fa.accept_15_7_10_3_1_2891 112
  130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 130 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 111 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 130 243 (accept_3_5 110 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 130 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 130 243 (Polychromatic418967fa.accept_17_6_11_5_1_3506 108 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 130 243 (accept_3_5 107 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 130 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 106 130
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 130 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 105 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 130 243 (accept_3_5 104 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 130 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 103 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 130 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313 102 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 130 243 (accept_3_5 101 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 130 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 100 130
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 130 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 99 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 130 243 (accept_3_5 98 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 130 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 130 243 (Polychromatic418967fa.accept_15_6_10_3_1_2844 96 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 130 243 (accept_3_5 95 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 130 243 (Polychromatic418967fa.accept_19_18_16_15_1_5044 94
  130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 130 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 130 243 (accept_3_5 92 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 130 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 130 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 90 130 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 130 243 (accept_3_5 89 130 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 130 243 (Polychromatic418967fa.accept_15_13_10_3_1_1952 88 130 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 130 243
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 87 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 130 243 (accept_3_5 86 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 130 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 130 243 (Polychromatic418967fa.accept_15_9_10_3_1_2845 84 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 130 243 (accept_3_5 83 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 130 243 (Polychromatic418967fa.accept_15_7_10_3_1_2891 82 130
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 130 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 130 243 (accept_3_5 80 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 130 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 130 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 130 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 130 243 (accept_3_5 77 130 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 130 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 130 243
  (Polychromatic418967fa.accept_17_7_11_5_1_3539 75 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 130 243 (accept_3_5 74 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 130 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 130 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 130 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 130 243 (accept_3_5 71 130 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 130 243 (Polychromatic418967fa.accept_16_6_2_3_1_4223 70 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 130 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 130 243 (accept_3_5 68 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 130 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 130 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 130 243 (accept_3_5 65 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 130 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 130 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 130 243
  (Polychromatic418967fa.accept_16_15_2_3_1_4262 63 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 130 243 (accept_3_5 62 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 130 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 130 243 (Polychromatic418967fa.accept_19_3_16_15_1_9281 60 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 130 243 (accept_3_5 59 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 130 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 130 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 130 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 130 243 (accept_3_5 56 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 130 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 130 243 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 130 243 (accept_3_5 53 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 130 243 (Polychromatic418967fa.accept_15_7_10_3_1_2891 52 130
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 130 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 130 243 (accept_3_5 50 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 130 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 130 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 130 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 130 243 (accept_3_5 47 130 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 130 243 (Polychromatic418967fa.accept_19_8_16_15_1_9249 46 130 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 130 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 130 243 (accept_3_5 44 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 130 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 130 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 130 243 (accept_3_5 41 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 130 243 (Polychromatic418967fa.accept_17_6_11_5_1_3506 40 130
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 130 243
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 39 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 130 243 (accept_3_5 38 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 130 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 130 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 130 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 130 243 (accept_3_5 35 130 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 130 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 130 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 130 243 (accept_3_5 32 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 130 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 130 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 130 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 130 243 (accept_3_5 29 130 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 130 243 (Polychromatic418967fa.accept_15_13_10_3_1_1952 28 130 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 130 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 130 243 (accept_3_5 26 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 130 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 130 243 (Polychromatic418967fa.accept_15_9_10_3_1_2845 24 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 130 243 (accept_3_5 23 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 130 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 130 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 130 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 130 243 (accept_3_5 20 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 130 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 130 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 130 243 (accept_3_5 17 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 130 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 130 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 130 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 130 243 (accept_3_5 14 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 130 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 130 243 (Polychromatic418967fa.accept_18_12_4_9_1_5452 12 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 130 243 (accept_3_5 11 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 130 243 (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 130
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 130 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 130 243 (accept_3_5 8 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  130 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 130 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 130 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 130 243 (accept_3_5 5 130 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 130 243 (Polychromatic418967fa.accept_25_4_5_18_1_14675 4 130 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 130 243
  (Polychromatic418967fa.accept_19_3_16_15_1_9281 3 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 130 243 (accept_3_5 2 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  130 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 130 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 130
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 115 129 243 (Eq.refl Bool.true) (allA_succ_of_gcd 114 129 243 3 38 43 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 129 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 113 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 129 243 (Polychromatic418967fa.accept_13_8_12_9_1_1168 112 129 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 129 243 3 37 43 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 129 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 110 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 129 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 109 129 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 129 243 3 36 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 129 243 (Polychromatic418967fa.accept_7_2_3_5_1_34
  107 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 129 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 106 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 129 243 3 35 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 129 243 (Polychromatic418967fa.accept_10_4_9_3_1_1907 104 129 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 129 243
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 103 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 129 243 3 34 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 129 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 101 129 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 129 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 100 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 129 243 3 33 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 129 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 129 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 129 243 (Polychromatic418967fa.accept_12_1_9_3_1_370
  97 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 129 243 3 32 43 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 129 243
  (Polychromatic418967fa.accept_12_11_9_3_1_792 95 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 129 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 129 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 129 243 3 31 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 129 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 92
  129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 129 243
  (Polychromatic418967fa.accept_12_7_9_3_1_767 91 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 129 243 3 30 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 129 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 89 129 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 129 243
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 88 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 87 129 243 3 29 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 86 129 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 129 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 85 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 129 243 3 28 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 129 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 83 129 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 82 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 129 243 3 27 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 129 243 (Polychromatic418967fa.accept_15_5_9_3_1_528 80 129 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 79
  129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 129 243 3 26 43 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 129 243
  (Polychromatic418967fa.accept_12_5_9_3_1_85 77 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 129 243 (Polychromatic418967fa.accept_10_6_9_3_1_935 76 129 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 129 243 3 25 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 129 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 74
  129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 73 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 129 243 3 24 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 129 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 129 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 70
  129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 129 243 3 23 43 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 129 243
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 68 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 129 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 67 129 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 129 243 3 22 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 129 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 65
  129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 64 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 129 243 3 21 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 129 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 129 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 243 (Polychromatic418967fa.accept_12_1_9_3_1_370
  61 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 129 243 3 20 43 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 129 243
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 59 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 129 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 129 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 129 243 3 19 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 129 243 (Polychromatic418967fa.accept_10_6_9_3_1_935
  56 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 243
  (Polychromatic418967fa.accept_12_7_9_3_1_767 55 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 129 243 3 18 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 129 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 129 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 243 (Polychromatic418967fa.accept_16_4_1_3_1_6581
  52 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 129 243 3 17 43 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 129 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 129 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 129 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 129 243 3 16 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 129 243 (Polychromatic418967fa.accept_12_11_9_3_1_792
  47 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 129 243 3 15 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 129 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 129 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 43
  129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 129 243 3 14 43 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 129 243
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 243 (Polychromatic418967fa.accept_14_12_3_5_1_1868 40 129 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 129 243 3 13 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 129 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 37 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 129 243 3 12 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 129 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 129 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 129 243 3 11 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 129 243 (Polychromatic418967fa.accept_17_15_10_5_1_1573 32 129 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 243
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 129 243 3 10 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 129 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 129 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 243
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 28 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 129 243 3 9 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 129 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 129 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 129
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 129 243 3 8 43 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 129 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 129 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 129 243 3 7 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 129 243 (Polychromatic418967fa.accept_15_5_9_3_1_528
  20 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 243
  (Polychromatic418967fa.accept_12_7_9_3_1_767 19 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 129 243 3 6 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 129 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 129 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 129 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 129 243 3 5 43 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 129 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 129 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 129 243 3 4 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 129 243 (Polychromatic418967fa.accept_12_11_9_3_1_792
  11 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 129 243 3 3 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 129 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 129 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 129 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 243 3 2 43 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 243
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 243 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 129 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 129 243 3 1 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 129 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 129 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 129
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 128 243 (Eq.refl Bool.true) (allA_succ_of_accept 115 128 243 (accept_3_4 115 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 128 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 114 128
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 113 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 128 243 (accept_3_4 112 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 128 243 (Polychromatic418967fa.accept_10_1_8_3_1_947 111 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 128 243 (Polychromatic418967fa.accept_15_5_8_3_1_556 110 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 128 243 (accept_3_4 109 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 128 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 108 128
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 107 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 128 243 (accept_3_4 106 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 128 243 (Polychromatic418967fa.accept_10_5_8_3_1_229 105 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 128 243 (Polychromatic418967fa.accept_29_17_12_11_1_14674 104 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 128 243 (accept_3_4 103 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 128 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 102 128
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 101 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 128 243 (accept_3_4 100 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 128 243 (Polychromatic418967fa.accept_13_8_11_9_1_593 99 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 128 243 (Polychromatic418967fa.accept_13_7_11_9_1_1858 98 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 128 243 (accept_3_4 97 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 128 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 96 128
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 128 243 (accept_3_4 94 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 128 243 (Polychromatic418967fa.accept_13_2_11_9_1_591 93 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 128 243 (Polychromatic418967fa.accept_13_1_11_9_1_1857 92 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 128 243 (accept_3_4 91 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 128 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 90 128 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 89 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 128 243 (accept_3_4 88 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 128 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 87 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 128 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 86 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 128 243 (accept_3_4 85 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 128 243 (Polychromatic418967fa.accept_15_9_8_3_1_557 84 128
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 128 243 (accept_3_4 82 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 128 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 81 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 128 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 80 128 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 128 243 (accept_3_4 79 128 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 128 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 78 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 128 243 (accept_3_4 76 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 128 243 (Polychromatic418967fa.accept_10_5_8_3_1_229 75 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 128 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 74 128 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 128 243 (accept_3_4 73 128 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 128 243 (Polychromatic418967fa.accept_11_6_7_1_1_564 72 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 128 243 (accept_3_4 70 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 128 243 (Polychromatic418967fa.accept_15_9_8_3_1_557 69 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 128 243 (Polychromatic418967fa.accept_19_11_14_15_1_9276 68 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 128 243 (accept_3_4 67 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 128 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 128 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 128 243 (accept_3_4 64 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 128 243 (Polychromatic418967fa.accept_14_7_2_5_1_4528 63 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 128 243 (Polychromatic418967fa.accept_29_4_12_11_1_14673 62 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 128 243 (accept_3_4 61 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 128 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 128 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 128 243 (accept_3_4 58 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 128 243 (Polychromatic418967fa.accept_15_12_8_3_1_1995 57 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 128 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 56 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 128 243 (accept_3_4 55 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 128 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 128 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 128 243 (accept_3_4 52 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 128 243 (Polychromatic418967fa.accept_10_1_8_3_1_947 51 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 128 243 (Polychromatic418967fa.accept_11_6_7_1_1_564 50 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 128 243 (accept_3_4 49 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 128 243 (Polychromatic418967fa.accept_17_14_9_5_1_4755 48 128
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 128 243 (accept_3_4 46 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 128 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 128 243 (Polychromatic418967fa.accept_24_20_8_3_1_14672 44 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 128 243 (accept_3_4 43 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 128 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 128 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 128 243 (accept_3_4 40 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 128 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 128 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 128 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 128 243 (accept_3_4 37 128 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 128 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 128 243 (accept_3_4 34 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 128 243 (Polychromatic418967fa.accept_13_7_11_9_1_1858 33 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 128 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 128 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 128 243 (accept_3_4 31 128 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 128 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 128 243 (accept_3_4 28 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 128 243 (Polychromatic418967fa.accept_13_1_11_9_1_1857 27 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 128 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 26 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 128 243 (accept_3_4 25 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 128 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 128 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 128 243 (accept_3_4 22 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 128 243 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 128 243 (Polychromatic418967fa.accept_13_7_11_9_1_1858 20 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 128 243 (accept_3_4 19 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 128 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 128 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 128 243 (accept_3_4 16 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 128 243 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 128 243 (Polychromatic418967fa.accept_13_1_11_9_1_1857 14 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 128 243 (accept_3_4 13 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 128 243 (Polychromatic418967fa.accept_15_12_8_3_1_1995 12 128
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 128 243 (accept_3_4 10 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  128 243 (Polychromatic418967fa.accept_15_9_8_3_1_557 9 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 128 243 (Polychromatic418967fa.accept_13_8_11_9_1_593 8 128 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 128 243 (accept_3_4 7 128 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 128 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 128 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 128 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 128 243 (accept_3_4 4 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  128 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 128 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 128 243 (Polychromatic418967fa.accept_13_2_11_9_1_591 2 128 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 128 243 (accept_3_4 1 128 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 128
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 117 127 243 (Eq.refl Bool.true) (allA_succ_of_accept 116 127 243 (accept_3_5 116 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 127 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 115 127
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 127 243
  (Polychromatic418967fa.accept_10_4_7_3_1_54 114 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 127 243 (accept_3_5 113 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 112 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 127 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 111 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 127 243 (accept_3_5 110 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 127 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 109 127
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 127 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 108 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 127 243 (accept_3_5 107 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 106 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 127 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 105 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 127 243 (accept_3_5 104 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 127 243 (Polychromatic418967fa.accept_13_12_10_9_1_1166 103
  127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 127 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 102 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 127 243 (accept_3_5 101 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 127 243 (Polychromatic418967fa.accept_19_4_13_15_1_3676 99 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 127 243 (accept_3_5 98 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 127 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 97 127 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 127 243
  (Polychromatic418967fa.accept_10_6_7_3_1_547 96 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 127 243 (accept_3_5 95 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 127 243 (Polychromatic418967fa.accept_11_5_6_1_1_988 93 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 127 243 (accept_3_5 92 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 127 243 (Polychromatic418967fa.accept_16_11_15_3_1_1304 91 127
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 127 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 90 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 127 243 (accept_3_5 89 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 127 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 127 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 127 243 (accept_3_5 86 127 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 127 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 85 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 127 243
  (Polychromatic418967fa.accept_8_4_7_3_1_144 84 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 127 243 (accept_3_5 83 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 127 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 81 127 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 127 243 (accept_3_5 80 127 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 127 243 (Polychromatic418967fa.accept_13_1_10_9_1_215 79 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 127 243
  (Polychromatic418967fa.accept_18_6_1_9_1_5551 78 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 127 243 (accept_3_5 77 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 127 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 75 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 127 243 (accept_3_5 74 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 127 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 127 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 127 243
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 72 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 127 243 (accept_3_5 71 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 127 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 127 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 127 243 (accept_3_5 68 127 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 127 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 127 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 66 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 127 243 (accept_3_5 65 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 127 243 (Polychromatic418967fa.accept_17_12_8_5_1_6018 63 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 127 243 (accept_3_5 62 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 127 243 (Polychromatic418967fa.accept_16_13_15_3_1_4196 61 127
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 127 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 60 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 127 243 (accept_3_5 59 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 127 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309 57 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 127 243 (accept_3_5 56 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 127 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 127 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 243
  (Polychromatic418967fa.accept_10_4_7_3_1_54 54 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 127 243 (accept_3_5 53 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 127 243 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 127 243 (accept_3_5 50 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 127 243 (Polychromatic418967fa.accept_11_5_6_1_1_988 49 127
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 127 243 (accept_3_5 47 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 127 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 127 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 243 (accept_3_5 44 127 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 243 (Polychromatic418967fa.accept_16_11_15_3_1_1304 43 127 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 243
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 42 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 127 243 (accept_3_5 41 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 127 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 127 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 243 (accept_3_5 38 127 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 243 (Polychromatic418967fa.accept_17_3_8_5_1_3636 37 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 243
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 127 243 (accept_3_5 35 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 127 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 243 (accept_3_5 32 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 127 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 243
  (Polychromatic418967fa.accept_17_13_8_5_1_3532 30 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 243 (accept_3_5 29 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 127 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 243 (accept_3_5 26 127 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 243 (accept_3_5 23 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 243 (accept_3_5 20 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 243 (Polychromatic418967fa.accept_13_6_10_9_1_4329 19 127
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 243 (accept_3_5 17 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 243 (accept_3_5 14 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 127 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 243
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 243 (accept_3_5 11 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 127 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 243 (accept_3_5 8 127 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 243 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 243 (accept_3_5 5 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 127 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 127 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 243 (accept_3_5 2 127 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 243 (Polychromatic418967fa.accept_13_1_10_9_1_215 1 127 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 118 126 243 (Eq.refl Bool.true) (allA_succ_of_gcd 117 126 243 9 13 14 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 126 243
  (Polychromatic418967fa.accept_11_6_5_1_1_586 116 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 126 243 (Polychromatic418967fa.accept_15_10_6_3_1_1160 115 126 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 126 243 3 38 42 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 126 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 113 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 126 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 112 126 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 126 243 3 37 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 126 243 (Polychromatic418967fa.accept_12_2_6_3_1_331
  110 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 126 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 109 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 126 243 9 12 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 126 243 (Polychromatic418967fa.accept_10_7_6_3_1_927 107 126 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 126 243
  (Polychromatic418967fa.accept_12_10_6_3_1_786 106 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 126 243 3 35 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 126 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 104 126 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 126 243
  (Polychromatic418967fa.accept_19_8_12_15_1_3703 103 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 126 243 3 34 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 126 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 126 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 126 243
  (Polychromatic418967fa.accept_12_4_6_3_1_332 100 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 126 243 9 11 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 126 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 98 126 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 126 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 97 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 126 243 3 32 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 126 243 (Polychromatic418967fa.accept_15_5_6_3_1_525 95 126 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 126 243 (Polychromatic418967fa.accept_11_6_5_1_1_586
  94 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 126 243 3 31 42 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 126 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 92 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 126 243 (Polychromatic418967fa.accept_15_1_6_3_1_2827 91 126 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 126 243 9 10 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 126 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 89
  126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 126 243
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 88 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 126 243 3 29 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 126 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 86 126 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 126 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 85
  126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 126 243 3 28 42 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 126 243
  (Polychromatic418967fa.accept_11_6_5_1_1_586 83 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 126 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 82 126 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 126 243 9 9 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 126 243 (Polychromatic418967fa.accept_12_8_6_3_1_366
  80 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 126 243
  (Polychromatic418967fa.accept_10_9_6_3_1_545 79 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 243 3 26 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 126 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 126 243 (Polychromatic418967fa.accept_12_4_6_3_1_332
  76 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 126 243 3 25 42 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 126 243
  (Polychromatic418967fa.accept_12_2_6_3_1_331 74 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 126 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 126 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 126 243 9 8 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 126 243 (Polychromatic418967fa.accept_15_11_6_3_1_1192
  71 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 126 243
  (Polychromatic418967fa.accept_12_10_6_3_1_786 70 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 126 243 3 23 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 126 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 68 126 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 126 243
  (Polychromatic418967fa.accept_10_7_6_3_1_927 67 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 243 3 22 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 126 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 126 243 (Polychromatic418967fa.accept_12_4_6_3_1_332
  64 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 126 243 9 7 14 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 126 243
  (Polychromatic418967fa.accept_12_2_6_3_1_331 62 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 126 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 126 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 126 243 3 20 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 126 243 (Polychromatic418967fa.accept_10_9_6_3_1_545
  59 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 126 243
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 58 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 126 243 3 19 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 126 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 56 126 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 126 243
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 55 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 243 9 6 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 126 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 126 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 126 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 52 126
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 126 243 3 17 42 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 126 243
  (Polychromatic418967fa.accept_11_6_5_1_1_586 50 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 126 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 126 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 126 243 3 16 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 126 243 (Polychromatic418967fa.accept_10_7_6_3_1_927
  47 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 126 243
  (Polychromatic418967fa.accept_12_10_6_3_1_786 46 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 126 243 9 5 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 126 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 126 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 126 243 (Polychromatic418967fa.accept_16_11_14_3_1_3140 43 126
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 126 243 3 14 42 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 126 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 126 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 126 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 126 243 3 13 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 126 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394
  38 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 126 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 243 9 4 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 126 243 (Polychromatic418967fa.accept_15_5_6_3_1_525 35 126 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 126 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 34 126
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 126 243 3 11 42 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 126 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 126 243 (Polychromatic418967fa.accept_15_1_6_3_1_2827 31 126 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 126 243 3 10 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 126 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 243
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 126 243 9 3 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 126 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 126 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 126 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 126 243 3 8 42 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 126 243
  (Polychromatic418967fa.accept_25_23_1_18_1_14671 23 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 126 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 126 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 126 243 3 7 42 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 126 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 126 243 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 126 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 126 243 9 2 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 126 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 243
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 126 243 3 5 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 126 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 126 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 126 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 126 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 243 3 4 42 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 243
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 126 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 126 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 126 243 9 1 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 126 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 126 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 243
  (Polychromatic418967fa.accept_10_7_6_3_1_927 7 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 243 3 2 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 126 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 126 243 3 1 42 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 126 243
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 126 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 126 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 126 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 126
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 125 243 (Eq.refl Bool.true) (allA_succ_of_accept 118 125 243 (accept_3_4 118 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 125 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 117 125
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 125 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 116 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 125 243 (accept_3_4 115 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 125 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 125 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 113 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 125 243 (accept_3_4 112 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 125 243 (Polychromatic418967fa.accept_13_7_8_9_1_1158 111 125
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 125 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 110 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 125 243 (accept_3_4 109 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 125 243 (Polychromatic418967fa.accept_10_8_5_3_1_543 108 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 125 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 107 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 125 243 (accept_3_4 106 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 125 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 105 125
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 125 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 104 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 125 243 (accept_3_4 103 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 125 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 125 243 (Polychromatic418967fa.accept_19_6_11_15_1_2527 101 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 125 243 (accept_3_4 100 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 125 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 99 125 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 125 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 125 243 (accept_3_4 97 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 125 243 (Polychromatic418967fa.accept_11_8_4_1_1_1000 96 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 125 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 95 125 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 125 243 (accept_3_4 94 125 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 125 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 93 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 125 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 125 243 (accept_3_4 91 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 125 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 125 243 (Polychromatic418967fa.accept_13_11_8_9_1_1161 89 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 125 243 (accept_3_4 88 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 125 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 87 125
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 125 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 125 243 (accept_3_4 85 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 125 243 (Polychromatic418967fa.accept_15_9_5_3_1_554 84 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 125 243 (Polychromatic418967fa.accept_15_8_5_3_1_1990 83 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 125 243 (accept_3_4 82 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 125 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 125 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 125 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 125 243 (accept_3_4 79 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 125 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 125 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 77 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 125 243 (accept_3_4 76 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 125 243 (Polychromatic418967fa.accept_20_15_5_3_1_1953 75 125
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 125 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 125 243 (accept_3_4 73 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 125 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 125 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 71 125 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 125 243 (accept_3_4 70 125 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 125 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 125 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 125 243 (accept_3_4 67 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 125 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 125 243 (Polychromatic418967fa.accept_16_1_13_3_1_2168 65 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 125 243 (accept_3_4 64 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 125 243 (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 125
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 125 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 125 243 (accept_3_4 61 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 125 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 125 243 (Polychromatic418967fa.accept_13_7_8_9_1_1158 59 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 125 243 (accept_3_4 58 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 125 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 125 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 125 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 125 243 (accept_3_4 55 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 125 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 125 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 125 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 243 (accept_3_4 52 125 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 125 243 (Polychromatic418967fa.accept_13_12_8_9_1_1833 51 125 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 125 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 125 243 (accept_3_4 49 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 125 243 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 125 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 47 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 243 (accept_3_4 46 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 125 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 125
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 125 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 125 243 (accept_3_4 43 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 125 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 243 (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 243 (accept_3_4 40 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 125 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 125 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 125 243 (accept_3_4 37 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 125 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 243 (Polychromatic418967fa.accept_17_1_6_5_1_3502 35 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 243 (accept_3_4 34 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 125
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 243 (accept_3_4 31 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 125 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 243 (accept_3_4 28 125 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 243 (accept_3_4 25 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 243 (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 243 (Polychromatic418967fa.accept_15_8_5_3_1_1990 23 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 243 (accept_3_4 22 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 125
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 243 (accept_3_4 19 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 243 (accept_3_4 16 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 125 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 243 (accept_3_4 13 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 125 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 243 (accept_3_4 10 125 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 243 (accept_3_4 7 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 243 (Polychromatic418967fa.accept_19_5_11_15_1_2460 5 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 243 (accept_3_4 4 125 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 243 (Polychromatic418967fa.accept_13_3_8_9_1_1134 3 125 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 243 (accept_3_4 1 125 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 120 124 243 (Eq.refl Bool.true) (allA_succ_of_accept 119 124 243 (accept_3_5 119 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 124 243 (Polychromatic418967fa.accept_19_4_10_15_1_9243 118
  124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 124 243
  (Polychromatic418967fa.accept_10_7_4_3_1_560 117 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 124 243 (accept_3_5 116 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 115 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 124 243 (Polychromatic418967fa.accept_12_6_4_3_1_361 114 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 124 243 (accept_3_5 113 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 124 243 (Polychromatic418967fa.accept_11_2_3_1_1_244 112 124
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 124 243
  (Polychromatic418967fa.accept_8_7_4_3_1_156 111 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 124 243 (accept_3_5 110 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 109 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 124 243 (Polychromatic418967fa.accept_13_4_7_9_1_5260 108 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 124 243 (accept_3_5 107 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 124 243 (Polychromatic418967fa.accept_13_2_7_9_1_2616 106 124
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 124 243
  (Polychromatic418967fa.accept_14_7_12_5_1_1861 105 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 124 243 (accept_3_5 104 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 103 124 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 124 243 (Polychromatic418967fa.accept_12_6_4_3_1_361 102 124
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 124 243 (accept_3_5 101 124
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 124 243
  (Polychromatic418967fa.accept_16_4_12_3_1_2180 100 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 124 243 (Polychromatic418967fa.accept_10_9_4_3_1_539 99 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 124 243 (accept_3_5 98 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 97 124 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 124 243
  (Polychromatic418967fa.accept_22_8_14_1_1_14629 96 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 124 243 (accept_3_5 95 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 124 243 (Polychromatic418967fa.accept_13_3_7_9_1_1153 94 124 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 124 243 (Polychromatic418967fa.accept_13_2_7_9_1_2616 93 124
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 124 243 (accept_3_5 92 124
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 124 243
  (Polychromatic418967fa.accept_6_1_4_3_1_14 91 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 124 243 (Polychromatic418967fa.accept_11_2_3_1_1_244 90 124 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 124 243 (accept_3_5 89 124 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 124 243 (Polychromatic418967fa.accept_16_8_12_3_1_4194 88 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 124 243
  (Polychromatic418967fa.accept_8_7_4_3_1_156 87 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 124 243 (accept_3_5 86 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 124 243 (Polychromatic418967fa.accept_13_6_7_9_1_1848 84 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 124 243 (accept_3_5 83 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 124 243 (Polychromatic418967fa.accept_13_4_7_9_1_5260 82 124
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 124 243
  (Polychromatic418967fa.accept_13_3_7_9_1_1153 81 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 124 243 (accept_3_5 80 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 124 243 (Polychromatic418967fa.accept_12_6_4_3_1_361 78 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 124 243 (accept_3_5 77 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 124 243 (Polychromatic418967fa.accept_13_11_7_9_1_612 76 124
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 124 243
  (Polychromatic418967fa.accept_22_9_14_1_1_14670 75 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 124 243 (accept_3_5 74 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 124 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 124 243 (Polychromatic418967fa.accept_16_8_12_3_1_4194 72 124
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 124 243 (accept_3_5 71 124
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 124 243
  (Polychromatic418967fa.accept_21_7_19_12_1_5579 70 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 124 243 (Polychromatic418967fa.accept_10_9_4_3_1_539 69 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 124 243 (accept_3_5 68 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 124 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 124 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 66 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 124 243 (accept_3_5 65 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 124 243 (Polychromatic418967fa.accept_21_1_19_12_1_5562 64 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 124 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 124 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 124 243 (accept_3_5 62 124 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 124 243
  (Polychromatic418967fa.accept_13_8_7_9_1_611 60 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 124 243 (accept_3_5 59 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 124 243 (Polychromatic418967fa.accept_13_6_7_9_1_1848 58 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 124 243 (Polychromatic418967fa.accept_10_7_4_3_1_560 57 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 124 243 (accept_3_5 56 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 124 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 124 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 54 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 124 243 (accept_3_5 53 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 124 243 (Polychromatic418967fa.accept_14_10_12_5_1_3466 52 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 124 243 (Polychromatic418967fa.accept_18_15_16_9_1_4299 51 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 124 243 (accept_3_5 50 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 124 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 124 243
  (Polychromatic418967fa.accept_18_12_16_9_1_4198 48 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 124 243 (accept_3_5 47 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 124 243 (Polychromatic418967fa.accept_11_2_3_1_1_244 46 124 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 124 243 (Polychromatic418967fa.accept_13_6_7_9_1_1848 45 124
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 124 243 (accept_3_5 44 124
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 124 243
  (Polychromatic418967fa.accept_6_1_4_3_1_14 43 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 124 243 (Polychromatic418967fa.accept_12_6_4_3_1_361 42 124 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 124 243 (accept_3_5 41 124 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 124 243 (Polychromatic418967fa.accept_16_8_12_3_1_4194 40 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 124 243
  (Polychromatic418967fa.accept_8_7_4_3_1_156 39 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 124 243 (accept_3_5 38 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 124 243 (Polychromatic418967fa.accept_16_4_12_3_1_2180 36 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 124 243 (accept_3_5 35 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 124 243 (Polychromatic418967fa.accept_13_8_7_9_1_611 34 124
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 124 243
  (Polychromatic418967fa.accept_18_15_16_9_1_4299 33 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 124 243 (accept_3_5 32 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 124 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 124 243 (Polychromatic418967fa.accept_12_6_4_3_1_361 30 124
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 124 243 (accept_3_5 29 124
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 124 243
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 28 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 124 243 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 124 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 124 243 (accept_3_5 26 124 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 124 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 124 243 (Polychromatic418967fa.accept_11_2_3_1_1_244
  24 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 124 243 (accept_3_5 23
  124 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 124 243
  (Polychromatic418967fa.accept_15_7_4_3_1_1930 22 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 124 243 (Polychromatic418967fa.accept_13_8_7_9_1_611 21 124 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 124 243 (accept_3_5 20 124 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 124 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 124 243 (Polychromatic418967fa.accept_12_6_4_3_1_361
  18 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 124 243 (accept_3_5 17
  124 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 124 243
  (Polychromatic418967fa.accept_13_3_7_9_1_1153 16 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 124 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 124 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 124 243 (accept_3_5 14 124 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 124 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 124 243
  (Polychromatic418967fa.accept_18_12_16_9_1_4198 12 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 124 243 (accept_3_5 11 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 124 243 (Polychromatic418967fa.accept_14_10_12_5_1_3466 10 124 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 124 243 (Polychromatic418967fa.accept_10_9_4_3_1_539 9
  124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 124 243 (accept_3_5 8 124
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14
  7 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 124 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 124 243 (accept_3_5 5 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  124 243 (Polychromatic418967fa.accept_13_4_7_9_1_5260 4 124 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 124 243 (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 124 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 124 243 (accept_3_5 2 124 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 124 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 124 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 121 123 243 (Eq.refl Bool.true) (allA_succ_of_gcd 120 123 243 3 40 41 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 123 243
  (Polychromatic418967fa.accept_13_2_6_9_1_2636 119 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 123 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 118 123 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 117 123 243 3 39 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 123 243
  (Polychromatic418967fa.accept_19_2_9_15_1_9238 116 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 123 243 (Polychromatic418967fa.accept_28_3_11_19_1_14669 115 123 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 123 243 3 38 41 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 123 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 113 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 123 243 (Polychromatic418967fa.accept_18_4_15_9_1_6882 112 123 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 123 243 3 37 41 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 123 243
  (Polychromatic418967fa.accept_16_14_11_3_1_4249 110 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 123 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 109 123 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 123 243 3 36 41 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 123 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 107 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 123 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 106 123 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 123 243 3 35 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 123 243 (Polychromatic418967fa.accept_7_6_4_5_1_314
  104 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 123 243
  (Polychromatic418967fa.accept_16_7_11_3_1_1330 103 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 123 243 3 34 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 123 243 (Polychromatic418967fa.accept_13_10_6_9_1_1152 101 123 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 123 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 100 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 123 243 3 33 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 123 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 98 123 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 97 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 123 243 3 32 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 123 243 (Polychromatic418967fa.accept_13_4_6_9_1_3401 95 123 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 123 243
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 94 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 123 243 3 31 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 123 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 92 123 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 243 (Polychromatic418967fa.accept_11_3_2_1_1_994
  91 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 123 243 3 30 41 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 123 243
  (Polychromatic418967fa.accept_18_17_15_9_1_5542 89 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 123 243 (Polychromatic418967fa.accept_13_10_6_9_1_1152 88 123 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 123 243 3 29 41 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 123 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 86 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 123 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 85 123 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 123 243 3 28 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 123 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 83
  123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 123 243
  (Polychromatic418967fa.accept_13_4_6_9_1_3401 82 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 123 243 3 27 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 123 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 80 123 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 243 (Polychromatic418967fa.accept_7_2_4_5_1_313
  79 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 123 243 3 26 41 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 123 243
  (Polychromatic418967fa.accept_18_5_15_9_1_1919 77 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 123 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 123 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 123 243 3 25 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 123 243 (Polychromatic418967fa.accept_17_6_4_5_1_3625
  74 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 243
  (Polychromatic418967fa.accept_23_4_8_13_1_8115 73 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 123 243 3 24 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 123 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 71 123 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 123 243
  (Polychromatic418967fa.accept_16_6_11_3_1_2198 70 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 123 243 3 23 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 123 243 (Polychromatic418967fa.accept_13_3_6_9_1_1150 68 123 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 243
  (Polychromatic418967fa.accept_13_2_6_9_1_2636 67 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 123 243 3 22 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 123 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 123 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 64
  123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 123 243 3 21 41 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 123 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 62 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 123 243 (Polychromatic418967fa.accept_19_4_9_15_1_6405 61 123 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 123 243 3 20 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 123 243 (Polychromatic418967fa.accept_13_7_6_9_1_1831
  59 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 58 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 123 243 3 19 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 123 243 (Polychromatic418967fa.accept_13_4_6_9_1_3401 56 123 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 55 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 123 243 3 18 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 123 243 (Polychromatic418967fa.accept_13_1_6_9_1_1197 53 123 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 243
  (Polychromatic418967fa.accept_17_1_4_5_1_3501 52 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 123 243 3 17 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 123 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 123 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 243
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 49 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 123 243 3 16 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 123 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 47 123 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 243 (Polychromatic418967fa.accept_13_7_6_9_1_1831
  46 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 123 243 3 15 41 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 123 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 44 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 123 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 123 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 123 243 3 14 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 123 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 41
  123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 243
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 40 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 123 243 3 13 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 123 243 (Polychromatic418967fa.accept_16_6_11_3_1_2198 38 123 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 123 243 3 12 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 123 243 (Polychromatic418967fa.accept_17_1_4_5_1_3501 35 123 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 34 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 123 243 3 11 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 123 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 123 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 243
  (Polychromatic418967fa.accept_16_15_11_3_1_2179 31 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 123 243 3 10 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 123 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 123 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 243
  (Polychromatic418967fa.accept_13_2_6_9_1_2636 28 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 123 243 3 9 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 123 243 (Polychromatic418967fa.accept_21_5_18_12_1_5531 26 123 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 243 (Polychromatic418967fa.accept_11_3_2_1_1_994
  25 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 123 243 3 8 41 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 123 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 123 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 123 243 3 7 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 123 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 20
  123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 243
  (Polychromatic418967fa.accept_21_19_18_12_1_10350 19 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 123 243 3 6 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 123 243 (Polychromatic418967fa.accept_13_4_6_9_1_3401 17 123 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 16 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 123 243 3 5 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 123 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 123 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 123 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 123 243 3 4 41 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 123 243
  (Polychromatic418967fa.accept_18_11_15_9_1_360 11 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 123 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 243 3 3 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 123 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 243
  (Polychromatic418967fa.accept_13_7_6_9_1_1831 7 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 123 243 3 2 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 123 243 (Polychromatic418967fa.accept_18_5_15_9_1_1919 5 123 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 243 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 123 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 123 243 3 1 41 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 123 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 123 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 123 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 123
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 122 243 (allA_succ_of_accept 121 122 243 (accept_3_4 121 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 122 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 120 122 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 122 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 119 122
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 122 243 (accept_3_4 118 122
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 122 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 117 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 122 243 (Polychromatic418967fa.accept_19_2_8_15_1_2447 116 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 122 243 (accept_3_4 115 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 122 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 114 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 122 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 113 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 122 243 (accept_3_4 112 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 122 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 111 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 122 243 (Polychromatic418967fa.accept_14_12_10_5_1_2712 110 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 122 243 (accept_3_4 109 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 122 243 (Polychromatic418967fa.accept_13_4_5_9_1_1829 108 122
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 122 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 107 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 122 243 (accept_3_4 106 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 122 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 122 243 (Polychromatic418967fa.accept_15_14_2_3_1_1980 104 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 122 243 (accept_3_4 103 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 122 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 102 122
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 122 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 122 243 (accept_3_4 100 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 122 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 99 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 122 243 (Polychromatic418967fa.accept_19_3_8_15_1_2523 98 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 122 243 (accept_3_4 97 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 122 243 (Polychromatic418967fa.accept_14_12_10_5_1_2712 96 122
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 122 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 122 243 (accept_3_4 94 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 122 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 122 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 92 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 122 243 (accept_3_4 91 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 122 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 90 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 122 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 122 243 (accept_3_4 88 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 122 243 (Polychromatic418967fa.accept_15_12_2_3_1_1146 87 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 122 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 86 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 122 243 (accept_3_4 85 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 122 243 (Polychromatic418967fa.accept_23_15_7_13_1_13029 84 122 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 122 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 122 243 (accept_3_4 82 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 122 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 122 243 (Polychromatic418967fa.accept_13_2_5_9_1_610 80 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 122 243 (accept_3_4 79 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 122 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 122 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 122 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 122 243 (accept_3_4 76 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 122 243 (Polychromatic418967fa.accept_10_5_2_3_1_239 75 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 122 243 (Polychromatic418967fa.accept_15_14_2_3_1_1980 74 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 122 243 (accept_3_4 73 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 122 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 122 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 122 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 122 243 (accept_3_4 70 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 122 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 122 243 (Polychromatic418967fa.accept_13_3_5_9_1_5285 68 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 122 243 (accept_3_4 67 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 122 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 122
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 122 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 122 243 (accept_3_4 64 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 122 243 (Polychromatic418967fa.accept_22_19_12_1_1_11606 63 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 62 122 243 (Polychromatic418967fa.accept_23_16_7_13_1_14626 62 122 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 122 243 (accept_3_4 61 122 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 122 243
  (Polychromatic418967fa.accept_16_12_10_3_1_4209 60 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 122 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 122 243 (accept_3_4 58 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 122 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 122 243
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 56 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 122 243 (accept_3_4 55 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 122 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 122 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 122 243 (accept_3_4 52 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 122 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 122 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 122 243 (accept_3_4 49 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 122 243 (Polychromatic418967fa.accept_21_6_17_12_1_10348 48 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 47 122 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 122 243 (accept_3_4 46 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 122 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 122 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 122 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 122 243 (accept_3_4 43 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 122 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 122 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 122 243 (accept_3_4 40 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 122 243 (Polychromatic418967fa.accept_16_7_10_3_1_2210 39 122 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 122 243
  (Polychromatic418967fa.accept_20_18_2_3_1_3169 38 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 122 243 (accept_3_4 37 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 122 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 122 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 122 243 (accept_3_4 34 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 122 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 122 243
  (Polychromatic418967fa.accept_24_8_2_3_1_11326 32 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 122 243 (accept_3_4 31 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 122 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 122 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 122 243 (accept_3_4 28 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 122 243 (Polychromatic418967fa.accept_13_1_5_9_1_226 27 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 243
  (Polychromatic418967fa.accept_14_12_10_5_1_2712 26 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 122 243 (accept_3_4 25 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 122 243 (Polychromatic418967fa.accept_18_6_14_9_1_3039 24 122 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 122 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 122 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 243 (accept_3_4 22 122 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 122 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 243
  (Polychromatic418967fa.accept_15_5_2_3_1_4876 20 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 122 243 (accept_3_4 19 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 122 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 122 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 243 (accept_3_4 16 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 122 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 243
  (Polychromatic418967fa.accept_13_1_5_9_1_226 14 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 122 243 (accept_3_4 13 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 122 243 (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 122 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 243 (accept_3_4 10 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 243 (accept_3_4 7 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 243 (accept_3_4 4 122 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 243 (Polychromatic418967fa.accept_13_3_5_9_1_5285 3 122 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 243 (accept_3_4 1 122 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 243 (allA_succ_of_accept 120 121 243 (Polychromatic418967fa.accept_22_10_11_1_1_14668 120 121 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 121 243 (accept_3_5 119 121 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27
  118 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 121 243
  (Polychromatic418967fa.accept_12_9_1_3_1_350 117 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 121 243 (accept_3_5 116 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 121 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 115 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 121 243 (accept_3_5 113 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 121 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 112 121
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 121 243
  (Polychromatic418967fa.accept_13_7_4_9_1_1865 111 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 121 243 (accept_3_5 110 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 121 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 109 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 121 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 108 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 121 243 (accept_3_5 107 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 121
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 121 243
  (Polychromatic418967fa.accept_12_9_1_3_1_350 105 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 121 243 (accept_3_5 104 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 121 243 (Polychromatic418967fa.accept_15_13_1_3_1_1972 103 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 121 243 (accept_3_5 101 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 121 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 121
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 121 243
  (Polychromatic418967fa.accept_13_8_4_9_1_1145 99 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 121 243 (accept_3_5 98 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 121 243 (Polychromatic418967fa.accept_13_6_4_9_1_4326 97 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 121 243 (Polychromatic418967fa.accept_13_5_4_9_1_601 96 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 121 243 (accept_3_5 95 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 121 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 121 243
  (Polychromatic418967fa.accept_12_9_1_3_1_350 93 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 121 243 (accept_3_5 92 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 121 243 (Polychromatic418967fa.accept_14_7_9_5_1_529 91 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 121 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 121 243 (accept_3_5 89 121 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 121 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 121 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 87 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 121 243 (accept_3_5 86 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 121 243 (Polychromatic418967fa.accept_13_7_4_9_1_1865 85 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 121 243 (Polychromatic418967fa.accept_13_6_4_9_1_4326 84 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 243 (accept_3_5 83 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 121 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 121 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 81 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 121 243 (accept_3_5 80 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 121 243 (Polychromatic418967fa.accept_15_4_1_3_1_1922 79 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 121 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 121 243 (accept_3_5 77 121 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 121 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 243
  (Polychromatic418967fa.accept_18_3_13_9_1_4260 75 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 121 243 (accept_3_5 74 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 121 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 73 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 121 243 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 243 (accept_3_5 71 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 121 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 243
  (Polychromatic418967fa.accept_12_9_1_3_1_350 69 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 121 243 (accept_3_5 68 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 121 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 121 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 121 243 (accept_3_5 65 121 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 121 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 243
  (Polychromatic418967fa.accept_14_7_9_5_1_529 63 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 121 243 (accept_3_5 62 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 121 243 (Polychromatic418967fa.accept_31_30_28_26_1_14667 61 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 121 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 243 (accept_3_5 59 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 121 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 243
  (Polychromatic418967fa.accept_12_9_1_3_1_350 57 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 243 (accept_3_5 56 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 243 (Polychromatic418967fa.accept_16_7_9_3_1_1324 55 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 121 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 243 (accept_3_5 53 121 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 243
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 51 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 243 (accept_3_5 50 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 243 (Polychromatic418967fa.accept_14_7_9_5_1_529 49 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 243 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 243 (accept_3_5 47 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 121 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 243 (accept_3_5 44 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 243 (Polychromatic418967fa.accept_15_13_1_3_1_1972 43 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 121 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 243 (accept_3_5 41 121 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 243 (accept_3_5 38 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 243 (Polychromatic418967fa.accept_17_3_2_5_1_2556 37 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 243 (Polychromatic418967fa.accept_15_6_1_3_1_2852 36 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 243 (accept_3_5 35 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 121 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 243
  (Polychromatic418967fa.accept_12_9_1_3_1_350 33 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 243 (accept_3_5 32 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 121 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 243 (accept_3_5 29 121 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 243
  (Polychromatic418967fa.accept_19_8_7_15_1_13364 27 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 121 243 (accept_3_5 26 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 121 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 121 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 121 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 243 (accept_3_5 23 121 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 22
  121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 243
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 243 (accept_3_5 20 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 243 (Polychromatic418967fa.accept_13_6_4_9_1_4326 19 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 121 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 243 (accept_3_5 17 121 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 121 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 243
  (Polychromatic418967fa.accept_22_15_11_1_1_6777 15 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 121 243 (accept_3_5 14 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 121 243 (Polychromatic418967fa.accept_15_13_1_3_1_1972 13 121 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 243 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 121
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 243 (accept_3_5 11 121
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 121 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 121 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 243 (accept_3_5 8 121 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 121 243 (Polychromatic418967fa.accept_13_7_4_9_1_1865 7 121 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 243 (accept_3_5 5 121
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 243 (Polychromatic418967fa.accept_6_4_1_3_1_77
  4 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 243 (accept_3_5 2 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 243 (Polychromatic418967fa.accept_25_1_21_18_1_9338 1 121 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 120 243 (allA_succ_of_accept 119 120 243 (Polychromatic418967fa.accept_11_9_10_1_1_581 119 120 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 120 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 118 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 117 120 243 3 39 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 116 120 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 116 120 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 120 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 115 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 120 243 3 38 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 120 243 (Polychromatic418967fa.accept_18_5_12_9_1_6871 113 120 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 120 243
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 112 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 111 120 243 3 37 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 110 120 243 (Polychromatic418967fa.accept_13_6_3_9_1_1827 110 120 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 120 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 109 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 120 243 3 36 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 120 243 (Polychromatic418967fa.accept_16_11_8_3_1_3183 107 120 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 120 243
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 106 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 120 243 3 35 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 120 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 104 120 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 120 243
  (Polychromatic418967fa.accept_13_12_3_9_1_4341 103 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 120 243 3 34 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 120 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 101 120 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 120 243
  (Polychromatic418967fa.accept_16_4_8_3_1_4206 100 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 120 243 3 33 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 120 243 (Polychromatic418967fa.accept_13_7_3_9_1_1142 98 120 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 120 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 97 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 120 243 3 32 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 120 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 95 120 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 120 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 94
  120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 120 243 3 31 40 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 120 243
  (Polychromatic418967fa.accept_16_12_8_3_1_4241 92 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 120 243 (Polychromatic418967fa.accept_16_11_8_3_1_3183 91 120 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 120 243 3 30 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 120 243 (Polychromatic418967fa.accept_17_4_1_5_1_2554
  89 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 120 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 88 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 120 243 3 29 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 120 243 (Polychromatic418967fa.accept_11_9_10_1_1_581 86 120 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 120 243
  (Polychromatic418967fa.accept_13_7_3_9_1_1142 85 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 120 243 3 28 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 120 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 83 120 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 120 243
  (Polychromatic418967fa.accept_18_10_12_9_1_2012 82 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 81 120 243 3 27 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 80 120 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 80 120 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 120 243
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 79 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 120 243 3 26 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 120 243 (Polychromatic418967fa.accept_13_12_3_9_1_4341 77 120 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 120 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 76 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 120 243 3 25 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 120 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 74 120 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 120 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 73
  120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 120 243 3 24 40 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 120 243
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 71 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 120 243 (Polychromatic418967fa.accept_13_5_3_9_1_1189 70 120 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 120 243 3 23 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 120 243 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  68 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 120 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 67 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 243 3 22 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 120 243 (Polychromatic418967fa.accept_18_11_12_9_1_992 65 120 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 120 243
  (Polychromatic418967fa.accept_11_9_10_1_1_581 64 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 120 243 3 21 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 120 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 62 120 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 120 243
  (Polychromatic418967fa.accept_16_13_8_3_1_5374 61 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 243 3 20 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 120 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 243 (Polychromatic418967fa.accept_13_6_3_9_1_1827
  58 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 120 243 3 19 40 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 120 243
  (Polychromatic418967fa.accept_21_14_15_12_1_5522 56 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 120 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 120 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 120 243 3 18 40 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 120 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 53 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 120 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 120 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 120 243 3 17 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 120 243 (Polychromatic418967fa.accept_17_16_1_5_1_2600
  50 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 120 243
  (Polychromatic418967fa.accept_19_11_6_15_1_14622 49 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 120 243 3 16 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 120 243 (Polychromatic418967fa.accept_13_8_3_9_1_5269 47 120 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 46 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 120 243 3 15 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 120 243 (Polychromatic418967fa.accept_13_5_3_9_1_1189 44 120 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 120 243
  (Polychromatic418967fa.accept_16_11_8_3_1_3183 43 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 243 3 14 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 120 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 243 (Polychromatic418967fa.accept_17_6_1_5_1_3552
  40 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 120 243 3 13 40 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 120 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 120 243 (Polychromatic418967fa.accept_16_5_8_3_1_4240 37 120 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 243 3 12 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 120 243 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  35 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 34 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 120 243 3 11 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 120 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 120 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 31
  120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 243 3 10 40 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 243
  (Polychromatic418967fa.accept_16_13_8_3_1_5374 29 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 120 243 (Polychromatic418967fa.accept_13_2_3_9_1_2610 28 120 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 120 243 3 9 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 120 243
  (Polychromatic418967fa.accept_21_5_15_12_1_5519 26 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 120 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 120 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 243 3 8 40 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 243
  (Polychromatic418967fa.accept_17_6_1_5_1_3552 23 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 120 243 (Polychromatic418967fa.accept_18_4_12_9_1_2011 22 120 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 120 243 3 7 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 120 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 20
  120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 243
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 19 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 243 3 6 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 120 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 243 (Polychromatic418967fa.accept_17_16_1_5_1_2600 16 120
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 120 243 3 5 40 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 120 243
  (Polychromatic418967fa.accept_21_14_15_12_1_5522 14 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 120 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 120 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 243 3 4 40 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 120 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 120 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 120 243 3 3 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 120 243 (Polychromatic418967fa.accept_13_8_3_9_1_5269 8 120 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 243
  (Polychromatic418967fa.accept_13_7_3_9_1_1142 7 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 120 243 3 2 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 120 243 (Polychromatic418967fa.accept_13_5_3_9_1_1189 5 120 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 120 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 120 243 3 1 40 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 120 243
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 120 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 120 243 (Polychromatic418967fa.accept_21_1_15_12_1_4007 1 120 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 120
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 243 (allA_succ_of_accept 118 119 243 (accept_3_4 118 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 117 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16
  116 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 119 243 (accept_3_4
  115 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 119 243
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 114 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 119 243 (Polychromatic418967fa.accept_21_8_14_12_1_4049 113 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 119 243 (accept_3_4 112 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 119 243 (Polychromatic418967fa.accept_13_7_2_9_1_1826 111 119 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 119 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 110 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 119 243 (accept_3_4 109 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 119 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 108 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 119 243 (Polychromatic418967fa.accept_13_3_2_9_1_1187 107 119 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 119 243 (accept_3_4 106 119 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 119 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 105 119
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 119 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 104 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 119 243 (accept_3_4 103 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 119 243 (Polychromatic418967fa.accept_13_11_2_9_1_2640 102 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 101 119 243 (Polychromatic418967fa.accept_15_11_14_3_1_1965 101 119 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 119 243 (accept_3_4 100 119 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 119 243
  (Polychromatic418967fa.accept_19_4_5_15_1_2437 99 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 98 119 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 119 243 (accept_3_4 97 119 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 119 243 (Polychromatic418967fa.accept_10_6_9_3_1_935 96 119 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 119 243
  (Polychromatic418967fa.accept_16_15_7_3_1_4273 95 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 119 243 (accept_3_4 94 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 119 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 93 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 119 243 (accept_3_4 91 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 119 243 (Polychromatic418967fa.accept_16_10_7_3_1_6601 90 119 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 119 243
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 89 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 119 243 (accept_3_4 88 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 119 243 (Polychromatic418967fa.accept_11_10_9_1_1_2186 87 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 86 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 119 243 (accept_3_4 85 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 119 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 119 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 119 243
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 83 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 119 243 (accept_3_4 82 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 119 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 81 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 119 243 (accept_3_4 79 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 119 243 (Polychromatic418967fa.accept_21_15_14_12_1_8736 78 119 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 119 243
  (Polychromatic418967fa.accept_15_2_14_3_1_1916 77 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 119 243 (accept_3_4 76 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 119 243 (Polychromatic418967fa.accept_16_11_7_3_1_3163 75 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 119 243 (accept_3_4 73 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 119 243 (Polychromatic418967fa.accept_13_7_2_9_1_1826 72 119 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 119 243
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 71 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 119 243 (accept_3_4 70 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 119 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 69 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 119 243 (accept_3_4 67 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 119 243 (Polychromatic418967fa.accept_10_6_9_3_1_935 66 119 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 119 243
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 65 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 119 243 (accept_3_4 64 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 119 243 (Polychromatic418967fa.accept_13_11_2_9_1_2640 63 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 243 (accept_3_4 61 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 119 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 119 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 243
  (Polychromatic418967fa.accept_13_7_2_9_1_1826 59 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 119 243 (accept_3_4 58 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 119 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 119 243 (accept_3_4 55 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 243 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 119 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 243
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 53 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 119 243 (accept_3_4 52 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 119 243 (Polychromatic418967fa.accept_14_9_7_5_1_1105 51 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 119 243 (accept_3_4 49 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 119 243 (Polychromatic418967fa.accept_18_12_11_9_1_4257 48 119 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 243
  (Polychromatic418967fa.accept_15_2_14_3_1_1916 47 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 119 243 (accept_3_4 46 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 119 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 243 (accept_3_4 43 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 119 243 (Polychromatic418967fa.accept_13_3_2_9_1_1187 42 119 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 243
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 41 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 119 243 (accept_3_4 40 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 119 243 (Polychromatic418967fa.accept_19_1_5_15_1_3722 39 119 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 119 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 243 (accept_3_4 37 119 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 243 (Polychromatic418967fa.accept_8_4_7_3_1_144
  36 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 243
  (Polychromatic418967fa.accept_22_13_9_1_1_11605 35 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 119 243 (accept_3_4 34 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 119 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 119 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 119 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 243 (accept_3_4 31 119 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 243 (Polychromatic418967fa.accept_14_2_7_5_1_5450
  30 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 243
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 29 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 119 243 (accept_3_4 28 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 119 243 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 243 (accept_3_4 25 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 243 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 119 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 243
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 23 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 243 (accept_3_4 22 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 243 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 243 (accept_3_4 19 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 243 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 119 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 243
  (Polychromatic418967fa.accept_15_2_14_3_1_1916 17 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 243 (accept_3_4 16 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 243 (Polychromatic418967fa.accept_16_15_7_3_1_4273 15 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 243 (accept_3_4 13 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 119 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 243
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 119 243 (accept_3_4 10 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  119 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 243 (accept_3_4 7 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 243 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 119 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 243
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 5 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 243 (accept_3_4 4 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 243 (Polychromatic418967fa.accept_13_3_2_9_1_1187 3 119 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 243 (accept_3_4 1 119 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 243 (allA_succ_of_accept 117 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 118 243 (accept_3_5 116 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 118 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 115 118
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 118 243
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 114 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 118 243 (accept_3_5 113 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 118 243 (Polychromatic418967fa.accept_13_8_1_9_1_1178 112 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 118 243 (Polychromatic418967fa.accept_10_1_8_3_1_947 111 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 118 243 (accept_3_5 110 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 118 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 118 243
  (Polychromatic418967fa.accept_19_13_4_15_1_7902 108 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 118 243 (accept_3_5 107 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 118 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 106 118 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 118 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 118 243 (accept_3_5 104 118 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 118 243 (Polychromatic418967fa.accept_6_1_4_3_1_14
  103 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 118 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 102 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 118 243 (accept_3_5 101 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 118 243 (Polychromatic418967fa.accept_15_10_13_3_1_4816 100 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 118 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 99 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 118 243 (accept_3_5 98 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 118 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 118 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 96 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 118 243 (accept_3_5 95 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 118 243 (Polychromatic418967fa.accept_19_18_4_15_1_3721 94 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 118 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 118 243 (accept_3_5 92 118 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 118 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 118 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 90 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 118 243 (accept_3_5 89 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 118 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 88 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 118 243 (Polychromatic418967fa.accept_15_12_13_3_1_1915 87 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 118 243 (accept_3_5 86 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 118 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 118 243
  (Polychromatic418967fa.accept_13_6_1_9_1_619 84 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 118 243 (accept_3_5 83 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 118 243 (Polychromatic418967fa.accept_16_2_6_3_1_5396 82 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 118 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 118 243 (accept_3_5 80 118 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 118 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 118 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 78 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 118 243 (accept_3_5 77 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 118 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 76 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 118 243 (Polychromatic418967fa.accept_10_5_8_3_1_229 75 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 118 243 (accept_3_5 74 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 118 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 118 243
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 72 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 118 243 (accept_3_5 71 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 118 243 (Polychromatic418967fa.accept_11_4_8_1_1_1047 70 118 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 118 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 118 243 (accept_3_5 68 118 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 118 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 67
  118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 118 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 66 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 118 243 (accept_3_5 65 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 118 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 118 243 (Polychromatic418967fa.accept_13_11_1_9_1_1179 63 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 118 243 (accept_3_5 62 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 118 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 118 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 118 243 (accept_3_5 59 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 118 243 (Polychromatic418967fa.accept_13_6_1_9_1_619 58 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 118 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 118 243 (accept_3_5 56 118 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 118 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 118 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 118 243 (accept_3_5 53 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 118 243 (Polychromatic418967fa.accept_16_4_6_3_1_1311 52 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 118 243 (Polychromatic418967fa.accept_10_1_8_3_1_947 51 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 118 243 (accept_3_5 50 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 118 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 118 243
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 118 243 (accept_3_5 47 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 118 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 118 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 118 243 (accept_3_5 44 118 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 118 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 118 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 118 243 (accept_3_5 41 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 118 243 (Polychromatic418967fa.accept_15_10_13_3_1_4816 40 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 118 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 118 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 243 (accept_3_5 38 118 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 118 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 118 243 (accept_3_5 35 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 118 243 (Polychromatic418967fa.accept_13_8_1_9_1_1178 34 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 118 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 243 (accept_3_5 32 118 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 118 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 118 243 (accept_3_5 29 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 118 243 (Polychromatic418967fa.accept_13_2_1_9_1_1174 28 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 118 243 (Polychromatic418967fa.accept_14_13_6_5_1_1853 27 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 243 (accept_3_5 26 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 118 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 243
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 24 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 118 243 (accept_3_5 23 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 118 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 118 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 243 (accept_3_5 20 118 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 118 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 118 243 (accept_3_5 17 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 118 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 243 (accept_3_5 14 118 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 243
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 118 243 (accept_3_5 11 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 118 243 (Polychromatic418967fa.accept_13_10_1_9_1_3380 10 118 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 243 (accept_3_5 8 118 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7
  118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 118 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 6 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 118 243 (accept_3_5 5 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  118 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 118 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 118 243 (Polychromatic418967fa.accept_21_3_13_12_1_2653 3 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 243 (accept_3_5 2 118 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 117 243 (allA_succ_of_accept 116 117 243 (Polychromatic418967fa.accept_10_6_7_3_1_547 116 117 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 243
  (Polychromatic418967fa.accept_10_5_7_3_1_561 115 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 117 243 3 38 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 117 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 113 117 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 117 243
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 112 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 111 117 243 3 37 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 110 117 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 110 117 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 109 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 117 243 9 12 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 117 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 107 117 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 117 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 106 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 117 243 3 35 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 117 243 (Polychromatic418967fa.accept_10_4_7_3_1_54 104 117 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 243
  (Polychromatic418967fa.accept_12_7_9_3_1_767 103 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 117 243 3 34 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 117 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 101 117 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 117 243
  (Polychromatic418967fa.accept_26_22_13_9_1_14666 100 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 99 117 243 9 11 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 98 117 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 117 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 97 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 117 243 3 32 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 117 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 95 117 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 94
  117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 117 243 3 31 39 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 117 243
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 92 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 117 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 91 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 117 243 9 10 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 117 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 89
  117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 243
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 88 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 87 117 243 3 29 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 86 117 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 117 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 243
  (Polychromatic418967fa.accept_10_5_7_3_1_561 85 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 117 243 3 28 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 117 243 (Polychromatic418967fa.accept_11_6_7_1_1_564 83 117 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 82
  117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 117 243 9 9 13 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 117 243
  (Polychromatic418967fa.accept_23_11_2_13_1_11441 80 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 117 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 79 117 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 117 243 3 26 39 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 117 243
  (Polychromatic418967fa.accept_12_5_9_3_1_85 77 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 243 (Polychromatic418967fa.accept_10_6_7_3_1_547 76 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 117 243 3 25 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 117 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 74
  117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 73 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 117 243 9 8 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 117 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 71 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 117 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 117 243 3 23 39 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 117 243
  (Polychromatic418967fa.accept_15_8_12_3_1_1912 68 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 117 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 67 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 117 243 3 22 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 117 243 (Polychromatic418967fa.accept_10_5_7_3_1_561
  65 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 243
  (Polychromatic418967fa.accept_10_4_7_3_1_54 64 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 117 243 9 7 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 117 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 243 (Polychromatic418967fa.accept_11_6_7_1_1_564 61 117
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 117 243 3 20 39 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 117 243
  (Polychromatic418967fa.accept_12_11_9_3_1_792 59 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 117 243 3 19 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 117 243 (Polychromatic418967fa.accept_10_6_7_3_1_547
  56 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 243
  (Polychromatic418967fa.accept_10_5_7_3_1_561 55 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 117 243 9 6 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 117 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 243 (Polychromatic418967fa.accept_15_7_12_3_1_1137 52 117
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 117 243 3 17 39 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 117 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 117 243 3 16 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 117 243 (Polychromatic418967fa.accept_12_11_9_3_1_792
  47 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 117 243 9 5 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 117 243 (Polychromatic418967fa.accept_10_4_7_3_1_54 44 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 117
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 117 243 3 14 39 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 117 243
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 243 (Polychromatic418967fa.accept_16_8_5_3_1_4297 40 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 117 243 3 13 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 117 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 37 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 117 243 9 4 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 117 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 35 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 117 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 117 243 3 11 39 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 117 243
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 32 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 243 3 10 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 29
  117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 243
  (Polychromatic418967fa.accept_11_6_7_1_1_564 28 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 117 243 9 3 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 117 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 117
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 243 3 8 39 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 243
  (Polychromatic418967fa.accept_12_11_9_3_1_792 23 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 243 3 7 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 243
  (Polychromatic418967fa.accept_25_20_17_18_1_14665 20 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 117 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 117 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 117 243 9 2 13 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 117 243
  (Polychromatic418967fa.accept_11_6_7_1_1_564 17 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 243 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 243 3 5 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 117 243 3 4 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 117 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 243 9 1 13 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 243
  (Polychromatic418967fa.accept_15_8_12_3_1_1912 8 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 243 3 2 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 117 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 243
  (Polychromatic418967fa.accept_10_4_7_3_1_54 4 117 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 117 243 3 1 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 117 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 117 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 243 (allA_succ_of_accept 115 116 243 (accept_3_4 115 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 116 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 114 116 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 116 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 113 116
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 116 243 (accept_3_4 112 116
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 116 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 111 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 116 243 (Polychromatic418967fa.accept_21_5_11_12_1_1479 110 116 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 116 243 (accept_3_4 109 116 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 116 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 108 116 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 107 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 116 243 (accept_3_4 106 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 116 243 (Polychromatic418967fa.accept_22_17_6_1_1_9971 105 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 116 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 104 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 116 243 (accept_3_4 103 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 116 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 102 116
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 101 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 116 243 (accept_3_4 100 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 116 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 99 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 116 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 98 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 116 243 (accept_3_4 97 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 116 243 (Polychromatic418967fa.accept_15_6_11_3_1_1172 96 116
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 116 243 (accept_3_4 94 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 116 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 93 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 116 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 92 116 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 116 243 (accept_3_4 91 116 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 116 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 90 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 89 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 116 243 (accept_3_4 88 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 116 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 87 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 116 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 86 116 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 116 243 (accept_3_4 85 116 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 116 243 (Polychromatic418967fa.accept_11_7_6_1_1_2182 84 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 116 243 (accept_3_4 82 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 116 243 (Polychromatic418967fa.accept_13_3_12_9_1_1193 81 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 116 243 (Polychromatic418967fa.accept_23_11_1_13_1_14664 80 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 116 243 (accept_3_4 79 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 116 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 116 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 116 243 (accept_3_4 76 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 116 243 (Polychromatic418967fa.accept_13_10_12_9_1_1837 75 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 116 243 (Polychromatic418967fa.accept_15_14_11_3_1_1957 74 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 116 243 (accept_3_4 73 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 116 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 116 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 116 243 (accept_3_4 70 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 116 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 116 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 68 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 116 243 (accept_3_4 67 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 116 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 116 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 116 243 (accept_3_4 64 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 116 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 116 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 62 116 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 116 243 (accept_3_4 61 116 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 116 243 (Polychromatic418967fa.accept_11_5_6_1_1_988 60 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 116 243 (accept_3_4 58 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 116 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 116 243 (Polychromatic418967fa.accept_16_8_4_3_1_3146 56 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 116 243 (accept_3_4 55 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 116 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 116 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 116 243 (accept_3_4 52 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 116 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 116 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 116 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 116 243 (accept_3_4 49 116 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 116 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 116 243 (accept_3_4 46 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 116 243 (Polychromatic418967fa.accept_21_3_11_12_1_10183 45 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 44 116 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 116 243 (accept_3_4 43 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 116 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 116 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 116 243 (accept_3_4 40 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 116 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 116 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 116 243 (accept_3_4 37 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 116 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 116 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 116 243 (accept_3_4 34 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 116 243 (Polychromatic418967fa.accept_16_1_4_3_1_3148 33 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 116 243 (Polychromatic418967fa.accept_19_13_2_15_1_7920 32 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 116 243 (accept_3_4 31 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 116 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 116 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 116 243 (accept_3_4 28 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 116 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 116 243 (Polychromatic418967fa.accept_17_9_14_5_1_1555 26 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 243 (accept_3_4 25 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 116 243 (Polychromatic418967fa.accept_16_8_4_3_1_3146 24 116
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 116 243 (accept_3_4 22 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 116 243 (Polychromatic418967fa.accept_13_8_12_9_1_1168 21 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 116 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 116 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 243 (accept_3_4 19 116 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 243 (accept_3_4 16 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 243 (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 243 (accept_3_4 13 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 243 (Polychromatic418967fa.accept_16_12_4_3_1_4295 12 116
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 243 (accept_3_4 10 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 116 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 243 (accept_3_4 7 116 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 116 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 243 (accept_3_4 4 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 243 (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 116 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 116 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 243 (accept_3_4 1 116 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 243 (allA_succ_of_accept 114 115 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 114 115 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 243 (accept_3_5 113 115 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 115 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 112 115
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 243
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 111 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 115 243 (accept_3_5 110 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 115 243 (Polychromatic418967fa.accept_19_14_1_15_1_7914 109 115 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 115 243 (Polychromatic418967fa.accept_10_8_5_3_1_543
  108 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 115 243 (accept_3_5
  107 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 115 243
  (Polychromatic418967fa.accept_6_4_1_3_1_77 106 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 115 243 (Polychromatic418967fa.accept_11_6_5_1_1_586 105 115 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 115 243 (accept_3_5 104 115 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 115 243 (Polychromatic418967fa.accept_15_13_10_3_1_1952 103 115 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 115 243
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 102 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 115 243 (accept_3_5 101 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 115 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 115 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 99 115 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 115 243 (accept_3_5 98 115 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 115 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 97 115 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 115 243
  (Polychromatic418967fa.accept_14_12_3_5_1_1868 96 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 115 243 (accept_3_5 95 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 115 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 115 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 93 115 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 115 243 (accept_3_5 92 115 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 115 243 (Polychromatic418967fa.accept_22_3_5_1_1_13187 91 115 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 115 243
  (Polychromatic418967fa.accept_19_14_1_15_1_7914 90 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 115 243 (accept_3_5 89 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 115 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 115 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 87 115
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 115 243 (accept_3_5 86 115
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 115 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 85 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 115 243 (Polychromatic418967fa.accept_15_9_10_3_1_2845 84 115 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 115 243 (accept_3_5 83 115 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 115 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 115 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  81 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 115 243 (accept_3_5 80
  115 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 115 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 79 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 115 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 115 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 115 243 (accept_3_5 77 115 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 115 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 115 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 115 243 (Polychromatic418967fa.accept_18_3_7_9_1_5486
  75 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 115 243 (accept_3_5 74
  115 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 115 243
  (Polychromatic418967fa.accept_13_8_11_9_1_593 73 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 115 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 115 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 115 243 (accept_3_5 71 115 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 115 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 115 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 115 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  69 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 115 243 (accept_3_5 68
  115 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 115 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 67 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 115 243 (Polychromatic418967fa.accept_13_1_11_9_1_1857 66 115 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 115 243 (accept_3_5 65 115 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 115 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 115 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 115 243
  (Polychromatic418967fa.accept_28_7_3_19_1_14663 63 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 115 243 (accept_3_5 62 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 115 243 (Polychromatic418967fa.accept_11_6_5_1_1_586 61 115 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 115 243 (Polychromatic418967fa.accept_13_8_11_9_1_593 60 115
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 115 243 (accept_3_5 59 115
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 243
  (Polychromatic418967fa.accept_6_4_1_3_1_77 58 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 115 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 115 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 243 (accept_3_5 56 115 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 115 243 (Polychromatic418967fa.accept_19_17_1_15_1_7901 55 115 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 115 243
  (Polychromatic418967fa.accept_13_2_11_9_1_591 54 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 115 243 (accept_3_5 53 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 115 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 115 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 115 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 243 (accept_3_5 50 115 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 115 243 (Polychromatic418967fa.accept_17_15_13_5_1_9877 49 115 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 243
  (Polychromatic418967fa.accept_10_8_5_3_1_543 48 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 115 243 (accept_3_5 47 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 115 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 115 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 115 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 243 (accept_3_5 44 115 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 115 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 243
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 115 243 (accept_3_5 41 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 115 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 115 243 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 115 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 243 (accept_3_5 38 115 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 115 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 115 243 (accept_3_5 35 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 115 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 115 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 115 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 243 (accept_3_5 32 115 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 243 (Polychromatic418967fa.accept_22_9_5_1_1_2204 31 115
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 115 243 (accept_3_5 29 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 115 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 115 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 115 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 243 (accept_3_5 26 115 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 243 (Polychromatic418967fa.accept_17_8_13_5_1_1597 25 115
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 243
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 24 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 243 (accept_3_5 23 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 115 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 243 (accept_3_5 20 115 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 243 (Polychromatic418967fa.accept_21_19_10_12_1_5550 19
  115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 243
  (Polychromatic418967fa.accept_10_8_5_3_1_543 18 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 243 (accept_3_5 17 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 115 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 243 (accept_3_5 14 115 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 243 (Polychromatic418967fa.accept_15_13_10_3_1_1952 13 115 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 243
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 243 (accept_3_5 11 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 115 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 243 (accept_3_5 8 115 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 115 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 243
  (Polychromatic418967fa.accept_11_6_5_1_1_586 6 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 243 (accept_3_5 5 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 115 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 243 (Polychromatic418967fa.accept_18_3_7_9_1_5486 3 115 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 243 (accept_3_5 2 115 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 115 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 243 (allA_succ_of_accept 113 114 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 113 114 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 114 243
  (Polychromatic418967fa.accept_12_4_6_3_1_332 112 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 111 114 243 3 37 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 110 114 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 110 114 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 114 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 109 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 114 243 3 36 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 114 243 (Polychromatic418967fa.accept_10_7_4_3_1_560 107 114 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 114 243
  (Polychromatic418967fa.accept_12_10_6_3_1_786 106 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 114 243 3 35 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 114 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 104 114 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 114 243
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 103 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 114 243 3 34 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 114 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 114 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 243
  (Polychromatic418967fa.accept_12_4_6_3_1_332 100 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 114 243 3 33 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 114 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 98 114 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 114 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 97
  114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 114 243 3 32 38 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 114 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 95 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 114 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 94 114 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 114 243 3 31 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 114 243 (Polychromatic418967fa.accept_12_8_6_3_1_366
  92 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 114 243
  (Polychromatic418967fa.accept_14_7_2_5_1_4528 91 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 243 3 30 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 114 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 114 243 (Polychromatic418967fa.accept_7_4_2_5_1_527
  88 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 114 243 3 29 38 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 114 243
  (Polychromatic418967fa.accept_12_2_6_3_1_331 86 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 114 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 114 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 114 243 3 28 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 114 243 (Polychromatic418967fa.accept_15_8_9_3_1_1194
  83 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 114 243
  (Polychromatic418967fa.accept_12_10_6_3_1_786 82 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 114 243 3 27 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 114 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 80 114 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 114 243 (Polychromatic418967fa.accept_10_9_4_3_1_539
  79 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 114 243 3 26 38 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 114 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 114 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 76 114 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 114 243 3 25 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 114 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 74
  114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 114 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 73 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 243 3 24 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 243 (Polychromatic418967fa.accept_13_6_10_9_1_4329 71 114 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 114 243
  (Polychromatic418967fa.accept_12_10_6_3_1_786 70 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 114 243 3 23 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 114 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 68 114 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 114 243 (Polychromatic418967fa.accept_7_4_2_5_1_527
  67 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 114 243 3 22 38 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 114 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 114 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 64 114 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 114 243 3 21 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 114 243 (Polychromatic418967fa.accept_12_2_6_3_1_331
  62 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 243 3 20 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 114 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 114 243 (Polychromatic418967fa.accept_12_10_6_3_1_786
  58 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 114 243 3 19 38 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 114 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 56 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 114 243 (Polychromatic418967fa.accept_15_10_9_3_1_1947 55 114 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 114 243 3 18 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 114 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 53
  114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 52 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 114 243 3 17 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 114 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 50 114 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 114 243 3 16 38 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 114 243
  (Polychromatic418967fa.accept_10_7_4_3_1_560 47 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 114 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 114 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 114 243 3 15 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 114 243 (Polychromatic418967fa.accept_12_8_6_3_1_366
  44 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 243
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 43 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 243 3 14 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 114 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 243 (Polychromatic418967fa.accept_12_4_6_3_1_332
  40 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 114 243 3 13 38 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 114 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 114 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 114 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 114 243 3 12 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 114 243 (Polychromatic418967fa.accept_14_7_2_5_1_4528
  35 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 243
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 114 243 3 11 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 114 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 114 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 243 (Polychromatic418967fa.accept_7_3_2_5_1_147
  31 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 114 243 3 10 38 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 114 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 114 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 114 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 114 243 3 9 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 114 243 (Polychromatic418967fa.accept_12_2_6_3_1_331
  26 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 243 3 8 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 114 243 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 114 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 114
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 114 243 3 7 38 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 114 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 114 243 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 114 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 114 243 3 6 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 114 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 243
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 114 243 3 5 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 114 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 114 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 114 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 243 3 4 38 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 114 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 114 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 114 243 3 3 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 114 243 (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 114 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 243
  (Polychromatic418967fa.accept_10_7_4_3_1_560 7 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 114 243 3 2 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 114 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 114 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 114 243 3 1 38 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 114 243
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 114 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 114 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 114
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 243 (allA_succ_of_accept 112 113 243 (accept_3_4 112 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 111 113 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 110 113
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 243 (accept_3_4 109 113
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 108 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 243 (Polychromatic418967fa.accept_19_12_18_15_1_10690 107 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 243 (accept_3_4 106 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 113 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 105 113 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 104 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 113 243 (accept_3_4 103 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 113 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 113 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 101 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 243 (accept_3_4 100 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 243 (Polychromatic418967fa.accept_15_9_8_3_1_557 99 113
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 243 (accept_3_4 97 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 243 (Polychromatic418967fa.accept_20_16_13_3_1_5974 96 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 95 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 243 (accept_3_4 94 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 93 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 113 243 (accept_3_4 91 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 113 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 113 243 (Polychromatic418967fa.accept_21_5_8_12_1_7108 89 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 243 (accept_3_4 88 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 113 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 243 (accept_3_4 85 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 243 (Polychromatic418967fa.accept_15_9_8_3_1_557 84 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 113 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 83 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 243 (accept_3_4 82 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 81 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 243 (accept_3_4 79 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 243 (Polychromatic418967fa.accept_16_13_1_3_1_2205 77 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 243 (accept_3_4 76 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 243 (Polychromatic418967fa.accept_17_7_11_5_1_3539 75 113
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 243 (accept_3_4 73 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 243 (Polychromatic418967fa.accept_15_12_8_3_1_1995 72 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 243 (Polychromatic418967fa.accept_15_11_8_3_1_1943 71 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 243 (accept_3_4 70 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 113 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 243 (accept_3_4 67 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 243 (Polychromatic418967fa.accept_15_5_8_3_1_556 65 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 243 (accept_3_4 64 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 243 (Polychromatic418967fa.accept_31_1_20_26_1_14662 63
  113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 243 (accept_3_4 61 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 243 (accept_3_4 58 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 243 (Polychromatic418967fa.accept_11_2_3_1_1_244 57 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 243 (accept_3_4 55 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 243 (accept_3_4 52 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 243 (Polychromatic418967fa.accept_18_15_5_9_1_5529 51 113 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 243 (accept_3_4 49 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 243 (Polychromatic418967fa.accept_19_9_18_15_1_3715 47 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 243 (accept_3_4 46 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 113 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 243 (accept_3_4 43 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 243 (accept_3_4 40 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 243 (accept_3_4 37 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 243 (Polychromatic418967fa.accept_16_4_1_3_1_6581 36 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 243 (Polychromatic418967fa.accept_11_2_3_1_1_244 35 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 243 (accept_3_4 34 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 113
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 243 (accept_3_4 31 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 243 (Polychromatic418967fa.accept_16_13_1_3_1_2205 29 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 243 (accept_3_4 28 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 113 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 243 (accept_3_4 25 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 243 (Polychromatic418967fa.accept_17_6_11_5_1_3506 23 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 243 (accept_3_4 22 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 113
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 243 (accept_3_4 19 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 243 (accept_3_4 16 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 243 (Polychromatic418967fa.accept_17_15_11_5_1_9866 15 113 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 243 (accept_3_4 13 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 243 (Polychromatic418967fa.accept_15_12_8_3_1_1995 12 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 243 (accept_3_4 10 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 243 (accept_3_4 7 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 243 (Polychromatic418967fa.accept_15_5_8_3_1_556 5 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 243 (accept_3_4 4 113 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 113 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 243 (accept_3_4 1 113 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 243 (allA_succ_of_accept 111 112 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 111 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 112 243 (accept_3_5 110 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 109 112
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 112 243
  (Polychromatic418967fa.accept_13_4_8_9_1_1156 108 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 112 243 (accept_3_5 107 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 112 243 (Polychromatic418967fa.accept_21_1_7_12_1_1465 106 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 112 243 (Polychromatic418967fa.accept_10_5_2_3_1_239 105 112 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 112 243 (accept_3_5 104 112 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14
  103 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 112 243
  (Polychromatic418967fa.accept_11_3_2_1_1_994 102 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 112 243 (accept_3_5 101 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 112 243 (Polychromatic418967fa.accept_15_10_7_3_1_1939 100 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 112 243 (Polychromatic418967fa.accept_17_14_10_5_1_8628 99 112 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 112 243 (accept_3_5 98 112 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 97
  112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 112 243
  (Polychromatic418967fa.accept_19_1_17_15_1_7897 96 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 112 243 (accept_3_5 95 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 112 243 (Polychromatic418967fa.accept_13_3_8_9_1_1134 94 112 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 112 243 (Polychromatic418967fa.accept_20_13_12_3_1_5972 93 112
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 112 243 (accept_3_5 92 112
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 112 243
  (Polychromatic418967fa.accept_6_1_4_3_1_14 91 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 112 243 (Polychromatic418967fa.accept_12_6_4_3_1_361 90 112 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 112 243 (accept_3_5 89 112 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 112 243 (Polychromatic418967fa.accept_19_12_17_15_1_6460 88 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 112 243
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 87 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 112 243 (accept_3_5 86 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 112 243 (Polychromatic418967fa.accept_18_12_4_9_1_5452 84 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 112 243 (accept_3_5 83 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 112 243 (Polychromatic418967fa.accept_13_4_8_9_1_1156 82 112
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 112 243
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 81 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 112 243 (accept_3_5 80 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 112 243 (Polychromatic418967fa.accept_12_6_4_3_1_361 78 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 112 243 (accept_3_5 77 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 112 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 76 112
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 112 243
  (Polychromatic418967fa.accept_10_5_2_3_1_239 75 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 112 243 (accept_3_5 74 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 112 243 (Polychromatic418967fa.accept_13_7_8_9_1_1158 72 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 112 243 (accept_3_5 71 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 112 243 (Polychromatic418967fa.accept_15_10_7_3_1_1939 70 112
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 112 243
  (Polychromatic418967fa.accept_11_3_2_1_1_994 69 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 112 243 (accept_3_5 68 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 112 243 (Polychromatic418967fa.accept_12_6_4_3_1_361 66 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 112 243 (accept_3_5 65 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 112 243 (Polychromatic418967fa.accept_13_12_8_9_1_1833 64 112
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 112 243
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 63 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 112 243 (accept_3_5 62 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 112 243 (Polychromatic418967fa.accept_19_3_17_15_1_6459 60 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 112 243 (accept_3_5 59 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 112 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 58 112
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 112 243
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 57 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 112 243 (accept_3_5 56 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 112 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 112 243 (accept_3_5 53 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 112 243 (Polychromatic418967fa.accept_19_14_17_15_1_3761 52
  112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 112 243
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 51 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 112 243 (accept_3_5 50 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 112 243 (Polychromatic418967fa.accept_17_14_10_5_1_8628 48 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 112 243 (accept_3_5 47 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 112 243 (Polychromatic418967fa.accept_13_7_8_9_1_1158 46 112
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 112 243
  (Polychromatic418967fa.accept_10_5_2_3_1_239 45 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 112 243 (accept_3_5 44 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 112 243 (Polychromatic418967fa.accept_12_6_4_3_1_361 42 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 112 243 (accept_3_5 41 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 112 243 (Polychromatic418967fa.accept_13_1_8_9_1_1154 40 112
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 112 243
  (Polychromatic418967fa.accept_19_1_17_15_1_7897 39 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 112 243 (accept_3_5 38 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 112 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 112 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 112
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 112 243 (accept_3_5 35 112
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 112 243
  (Polychromatic418967fa.accept_15_4_7_3_1_119 34 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 112 243 (Polychromatic418967fa.accept_13_7_8_9_1_1158 33 112 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 112 243 (accept_3_5 32 112 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 112 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 112 243 (Polychromatic418967fa.accept_12_6_4_3_1_361
  30 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 243 (accept_3_5 29
  112 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 112 243
  (Polychromatic418967fa.accept_22_6_2_1_1_6763 28 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 112 243 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 112 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 112 243 (accept_3_5 26 112 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 112 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 112 243
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 112 243 (accept_3_5 23 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 112 243 (Polychromatic418967fa.accept_19_3_17_15_1_6459 22 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 112 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 112 243 (accept_3_5 20 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 112 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 112 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 112 243 (accept_3_5 17 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 112 243 (Polychromatic418967fa.accept_13_3_8_9_1_1134 16 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 112 243 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 112 243 (accept_3_5 14 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 112 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 243
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 112 243 (accept_3_5 11 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 112 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 112 243 (Polychromatic418967fa.accept_20_9_12_3_1_3191 9 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 112 243 (accept_3_5 8 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 112 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 112 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 112 243 (accept_3_5 5 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  112 243 (Polychromatic418967fa.accept_13_4_8_9_1_1156 4 112 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 112 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 112 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 243 (accept_3_5 2 112 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 112 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 112 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 243 (allA_succ_of_accept 110 111 243 (Polychromatic418967fa.accept_13_6_7_9_1_1848 110 111 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 109 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 111 243 3 36 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 111 243 (Polychromatic418967fa.accept_13_3_7_9_1_1153 107 111 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 111 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 106 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 111 243 3 35 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 111 243 (Polychromatic418967fa.accept_14_6_13_5_1_534 104 111 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 243
  (Polychromatic418967fa.accept_16_7_15_3_1_1302 103 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 111 243 3 34 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 111 243 (Polychromatic418967fa.accept_15_11_6_3_1_1192 101 111 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 111 243
  (Polychromatic418967fa.accept_8_4_7_3_1_144 100 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 111 243 3 33 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 111 243 (Polychromatic418967fa.accept_10_8_1_3_1_1374 98 111 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 243
  (Polychromatic418967fa.accept_13_6_7_9_1_1848 97 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 111 243 3 32 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 111 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 95 111 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 111 243 (Polychromatic418967fa.accept_13_3_7_9_1_1153
  94 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 111 243 3 31 37 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 111 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 92 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 111 243 (Polychromatic418967fa.accept_15_1_6_3_1_2827 91 111 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 111 243 3 30 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 111 243 (Polychromatic418967fa.accept_13_11_7_9_1_612
  89 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 111 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 88 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 111 243 3 29 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 111 243 (Polychromatic418967fa.accept_13_8_7_9_1_611 86 111 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 85
  111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 111 243 3 28 37 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 111 243
  (Polychromatic418967fa.accept_25_8_11_18_1_14661 83 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 111 243 (Polychromatic418967fa.accept_10_2_1_3_1_233 82 111 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 111 243 3 27 37 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 111 243
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 80 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 111 243 (Polychromatic418967fa.accept_18_7_3_9_1_1020 79 111 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 111 243 3 26 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 111 243
  (Polychromatic418967fa.accept_16_13_15_3_1_4196 77 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 111 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 76 111 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 111 243 3 25 37 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 111 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 74 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 111 243 (Polychromatic418967fa.accept_13_8_7_9_1_611 73 111 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 111 243 3 24 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 111 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 71
  111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 243
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 70 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 111 243 3 23 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 111 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 68 111 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 243 (Polychromatic418967fa.accept_7_4_6_5_1_141
  67 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 111 243 3 22 37 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 111 243
  (Polychromatic418967fa.accept_15_5_6_3_1_525 65 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 111 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 111 243 3 21 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 111 243 (Polychromatic418967fa.accept_10_2_1_3_1_233
  62 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 243
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 61 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 111 243 3 20 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 111 243 (Polychromatic418967fa.accept_16_11_15_3_1_1304 59 111 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 243
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 58 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 111 243 3 19 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 111 243 (Polychromatic418967fa.accept_13_4_7_9_1_5260 56 111 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 243
  (Polychromatic418967fa.accept_13_3_7_9_1_1153 55 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 111 243 3 18 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 111 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 111 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 243 (Polychromatic418967fa.accept_8_4_7_3_1_144
  52 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 111 243 3 17 37 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 111 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 50 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 243 (Polychromatic418967fa.accept_18_13_3_9_1_4233 49 111 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 111 243 3 16 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 111 243 (Polychromatic418967fa.accept_13_8_7_9_1_611
  47 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 46 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 111 243 3 15 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 111 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 111 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 43
  111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 111 243 3 14 37 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 111 243
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 41 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 243 (Polychromatic418967fa.accept_15_10_6_3_1_1160 40 111 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 111 243 3 13 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 111 243 (Polychromatic418967fa.accept_10_8_1_3_1_1374
  38 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 243
  (Polychromatic418967fa.accept_13_11_7_9_1_612 37 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 111 243 3 12 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 111 243 (Polychromatic418967fa.accept_15_5_6_3_1_525 35 111 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 243 (Polychromatic418967fa.accept_13_8_7_9_1_611
  34 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 111 243 3 11 37 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 111 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 111 243 (Polychromatic418967fa.accept_15_1_6_3_1_2827 31 111 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 111 243 3 10 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 111 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 29
  111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 243
  (Polychromatic418967fa.accept_8_4_7_3_1_144 28 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 111 243 3 9 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 111 243 (Polychromatic418967fa.accept_15_11_6_3_1_1192 26 111 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 111 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 243 3 8 37 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 243
  (Polychromatic418967fa.accept_16_7_15_3_1_1302 23 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 111 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 243 3 7 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 20
  111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 243
  (Polychromatic418967fa.accept_13_6_7_9_1_1848 19 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 111 243 3 6 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 111 243 (Polychromatic418967fa.accept_13_4_7_9_1_5260 17 111 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 243 (Polychromatic418967fa.accept_13_3_7_9_1_1153 16 111
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 243 3 5 37 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 243
  (Polychromatic418967fa.accept_17_14_9_5_1_4755 14 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 243 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 111 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 243 3 4 37 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 243 (Polychromatic418967fa.accept_15_10_6_3_1_1160 10 111 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 243 3 3 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 111 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 243
  (Polychromatic418967fa.accept_16_7_15_3_1_1302 7 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 111 243 3 2 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 111 243 (Polychromatic418967fa.accept_15_5_6_3_1_525 5 111 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 111 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 243 3 1 37 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 243
  (Polychromatic418967fa.accept_10_2_1_3_1_233 2 111 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 111 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 111
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 243 (allA_succ_of_accept 109 110 243 (accept_3_4 109 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 110 243 (Polychromatic418967fa.accept_13_4_6_9_1_3401 108 110 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 110 243 (Polychromatic418967fa.accept_6_5_2_3_1_81
  107 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 110 243 (accept_3_4
  106 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 110 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 105 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 110 243 (Polychromatic418967fa.accept_23_12_18_13_1_14660 104 110 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 110 243 (accept_3_4 103 110 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 110 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 102 110 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 110 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 110 243 (accept_3_4 100 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 110 243 (Polychromatic418967fa.accept_15_9_5_3_1_554 99 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 110 243 (Polychromatic418967fa.accept_13_7_6_9_1_1831 98 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 110 243 (accept_3_4 97 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 110 243 (Polychromatic418967fa.accept_15_6_5_3_1_1988 96 110
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 110 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 110 243 (accept_3_4 94 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 110 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 110 243 (Polychromatic418967fa.accept_13_1_6_9_1_1197 92 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 110 243 (accept_3_4 91 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 110 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 90 110
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 110 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 110 243 (accept_3_4 88 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 110 243 (Polychromatic418967fa.accept_14_3_12_5_1_153 87 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 110 243 (Polychromatic418967fa.accept_25_11_10_18_1_14659 86 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 110 243 (accept_3_4 85 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 110 243 (Polychromatic418967fa.accept_15_9_5_3_1_554 84 110
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 110 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 110 243 (accept_3_4 82 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 110 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 110 243 (Polychromatic418967fa.accept_13_2_6_9_1_2636 80 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 110 243 (accept_3_4 79 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 110 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 78 110
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 110 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 110 243 (accept_3_4 76 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 110 243 (Polychromatic418967fa.accept_13_10_6_9_1_1152 75 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 110 243 (Polychromatic418967fa.accept_21_11_5_12_1_10218 74 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 110 243 (accept_3_4 73 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 110 243 (Polychromatic418967fa.accept_13_7_6_9_1_1831 72 110
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 110 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 110 243 (accept_3_4 70 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 110 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 110 243 (Polychromatic418967fa.accept_13_3_6_9_1_1150 68 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 110 243 (accept_3_4 67 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 110 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 110
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 110 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 110 243 (accept_3_4 64 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 110 243 (Polychromatic418967fa.accept_14_7_12_5_1_1861 63 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 110 243 (Polychromatic418967fa.accept_13_10_6_9_1_1152 62 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 110 243 (accept_3_4 61 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 110 243 (Polychromatic418967fa.accept_18_6_2_9_1_3056 60 110
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 110 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 110 243 (accept_3_4 58 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 110 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 110 243 (Polychromatic418967fa.accept_13_4_6_9_1_3401 56 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 110 243 (accept_3_4 55 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 110 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 110
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 110 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 110 243 (accept_3_4 52 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 110 243 (Polychromatic418967fa.accept_15_6_5_3_1_1988 51 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 110 243 (Polychromatic418967fa.accept_21_8_5_12_1_10219 50 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 110 243 (accept_3_4 49 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 110 243 (Polychromatic418967fa.accept_21_6_5_12_1_10314 48 110
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 110 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 110 243 (accept_3_4 46 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 110 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 110 243 (Polychromatic418967fa.accept_26_18_6_9_1_14658 44 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 110 243 (accept_3_4 43 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 110 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 110
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 110 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 110 243 (accept_3_4 40 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 110 243 (Polychromatic418967fa.accept_15_9_5_3_1_554 39 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 110 243 (Polychromatic418967fa.accept_14_10_12_5_1_3466 38 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 243 (accept_3_4 37 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 110 243 (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 110
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 110 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 110 243 (accept_3_4 34 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 110 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 110 243 (Polychromatic418967fa.accept_15_2_5_3_1_552 32 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 110 243 (accept_3_4 31 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 110 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 110
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 110 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 110 243 (accept_3_4 28 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 110 243 (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 110 243 (Polychromatic418967fa.accept_29_26_23_11_1_14657 26 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 110 243 (accept_3_4 25 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 110 243 (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 110
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 110 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 110 243 (accept_3_4 22 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 110 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 110 243 (Polychromatic418967fa.accept_13_7_6_9_1_1831 20 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 110 243 (accept_3_4 19 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 110
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 110 243 (accept_3_4 16 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 110 243 (Polychromatic418967fa.accept_13_2_6_9_1_2636 15 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 110 243 (Polychromatic418967fa.accept_13_1_6_9_1_1197 14 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 243 (accept_3_4 13 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 110 243 (Polychromatic418967fa.accept_17_12_8_5_1_6018 12 110
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 110 243 (accept_3_4 10 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  110 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 110 243 (Polychromatic418967fa.accept_15_8_5_3_1_1990 8 110 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 243 (accept_3_4 7 110 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 110 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 110 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 110 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 110 243 (accept_3_4 4 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  110 243 (Polychromatic418967fa.accept_13_3_6_9_1_1150 3 110 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 110 243 (Polychromatic418967fa.accept_13_2_6_9_1_2636 2 110 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 243 (accept_3_4 1 110 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 243 (allA_succ_of_accept 108 109 243 (Polychromatic418967fa.accept_11_9_10_1_1_581 108 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 243 (accept_3_5 107 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 109 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 109
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 243
  (Polychromatic418967fa.accept_12_9_1_3_1_350 105 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 243 (accept_3_5 104 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 243 (Polychromatic418967fa.accept_21_19_4_12_1_4027 103 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 109 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 243 (accept_3_5 101 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 109
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 99 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 243 (accept_3_5 98 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 97 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 243 (Polychromatic418967fa.accept_10_6_9_3_1_935 96 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 243 (accept_3_5 95 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 109 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 93 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 243 (accept_3_5 92 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 243 (Polychromatic418967fa.accept_15_1_4_3_1_1928 91 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 109 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 109 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 243 (accept_3_5 89 109 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 243
  (Polychromatic418967fa.accept_19_11_14_15_1_9276 87 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 109 243 (accept_3_5 86 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 109 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 85 109 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 109 243 (Polychromatic418967fa.accept_10_4_9_3_1_1907 84 109
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 243 (accept_3_5 83 109
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 82 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 109 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 81 109 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 109 243 (accept_3_5 80 109 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 109 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 79 109 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 109 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 78
  109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 243 (accept_3_5 77
  109 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 243
  (Polychromatic418967fa.accept_6_4_1_3_1_77 76 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 109 243 (Polychromatic418967fa.accept_11_9_10_1_1_581 75 109 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 109 243 (accept_3_5 74 109 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 109 243 (Polychromatic418967fa.accept_23_4_17_13_1_14656 73 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 109 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 72 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 109 243 (accept_3_5 71 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 109 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 109 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 109 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 109 243 (accept_3_5 68 109 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 109 243 (Polychromatic418967fa.accept_13_2_5_9_1_610 67 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 109 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 109 243 (accept_3_5 65 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 109 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 109 243 (Polychromatic418967fa.accept_16_15_13_3_1_4215 63 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 109 243 (accept_3_5 62 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 109 243 (Polychromatic418967fa.accept_15_1_4_3_1_1928 61 109
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 109 243
  (Polychromatic418967fa.accept_17_9_7_5_1_1566 60 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 109 243 (accept_3_5 59 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 109 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 109 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 109 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 109 243 (accept_3_5 56 109 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 109 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 109 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 109 243 (accept_3_5 53 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 109 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 109 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 109 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 243 (accept_3_5 50 109 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 109 243 (Polychromatic418967fa.accept_16_1_13_3_1_2168 49 109 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 109 243 (accept_3_5 47 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 109 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 109 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 109 243 (accept_3_5 44 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 109 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 109 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 243 (accept_3_5 41 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 243 (Polychromatic418967fa.accept_18_3_1_9_1_1929 39 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 243 (accept_3_5 38 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 109 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 243 (accept_3_5 35 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 243 (accept_3_5 32 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 243 (Polychromatic418967fa.accept_11_9_10_1_1_581 31 109
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 243 (accept_3_5 29 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 109 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 243 (accept_3_5 26 109 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 243 (Polychromatic418967fa.accept_31_25_16_26_1_14655 25 109 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 243
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 243 (accept_3_5 23 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 243 (accept_3_5 20 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 243 (Polychromatic418967fa.accept_20_19_9_3_1_10554 19 109
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 243 (accept_3_5 17 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 109 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 243 (accept_3_5 14 109 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 243
  (Polychromatic418967fa.accept_17_12_7_5_1_8659 12 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 243 (accept_3_5 11 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 109 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 243 (accept_3_5 8 109 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 243 (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 243 (accept_3_5 5 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 109 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 243 (Polychromatic418967fa.accept_13_3_5_9_1_5285 3 109 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 243 (accept_3_5 2 109 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 109 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 243 (allA_succ_of_accept 107 108 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 107 108 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 108 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 106 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 108 243 3 35 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 108 243 (Polychromatic418967fa.accept_16_8_12_3_1_4194 104 108 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 108 243
  (Polychromatic418967fa.accept_8_7_4_3_1_156 103 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 108 243 3 34 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 108 243 (Polychromatic418967fa.accept_10_1_8_3_1_947 101 108 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 108 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 100 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 108 243 9 11 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 108 243 (Polychromatic418967fa.accept_11_10_9_1_1_2186 98 108 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 108 243
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 97 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 243 3 32 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 108 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 95 108 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 243
  (Polychromatic418967fa.accept_20_14_8_3_1_6011 94 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 108 243 3 31 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 108 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 92 108 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 108 243 (Polychromatic418967fa.accept_10_1_8_3_1_947
  91 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 108 243 9 10 12 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 108 243
  (Polychromatic418967fa.accept_16_9_12_3_1_3138 89 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 108 243 (Polychromatic418967fa.accept_16_8_12_3_1_4194 88 108 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 108 243 3 29 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 108 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 86
  108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 108 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 85 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 243 3 28 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 243 (Polychromatic418967fa.accept_13_5_4_9_1_601 83 108 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 108 243
  (Polychromatic418967fa.accept_14_12_10_5_1_2712 82 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 81 108 243 27 3 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 108 243 (Polychromatic418967fa.accept_19_4_13_15_1_3676 80 108 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 108 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 79 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 243 3 26 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 243 (Polychromatic418967fa.accept_21_14_3_12_1_10169 77 108 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 108 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 76 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 108 243 3 25 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 108 243 (Polychromatic418967fa.accept_16_10_12_3_1_4252 74 108 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 108 243
  (Polychromatic418967fa.accept_13_8_4_9_1_1145 73 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 243 9 8 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 108 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 108 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 243 (Polychromatic418967fa.accept_13_5_4_9_1_601 70 108
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 108 243 3 23 36 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 108 243
  (Polychromatic418967fa.accept_14_12_10_5_1_2712 68 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 108 243 (Polychromatic418967fa.accept_21_4_3_12_1_10266 67 108 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 108 243 3 22 36 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 108 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 65 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 108 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 108 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 108 243 9 7 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 108 243 (Polychromatic418967fa.accept_17_11_6_5_1_3662
  62 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 108 243
  (Polychromatic418967fa.accept_10_1_8_3_1_947 61 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 243 3 20 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 243 (Polychromatic418967fa.accept_13_7_4_9_1_1865 59 108 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 58 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 108 243 3 19 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 108 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 56 108 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 243 (Polychromatic418967fa.accept_8_7_4_3_1_156
  55 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 108 243 27 2 4 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 108 243
  (Polychromatic418967fa.accept_20_13_8_3_1_11818 53 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 108 243 (Polychromatic418967fa.accept_16_4_12_3_1_2180 52 108 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 108 243 3 17 36 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 108 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 108 243 (Polychromatic418967fa.accept_21_7_3_12_1_1455 49 108 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 108 243 3 16 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 108 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 47
  108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 46 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 108 243 9 5 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 108 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 108 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 108 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 108 243 3 14 36 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 108 243
  (Polychromatic418967fa.accept_10_1_8_3_1_947 41 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 108 243 (Polychromatic418967fa.accept_14_12_10_5_1_2712 40 108 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 108 243 3 13 36 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 108 243
  (Polychromatic418967fa.accept_17_4_6_5_1_9871 38 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 108 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 108 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 108 243 9 4 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 108 243 (Polychromatic418967fa.accept_10_5_8_3_1_229
  35 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 243
  (Polychromatic418967fa.accept_13_8_4_9_1_1145 34 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 108 243 3 11 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 108 243 (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 108 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 243
  (Polychromatic418967fa.accept_8_7_4_3_1_156 31 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 243 3 10 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 108 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 243
  (Polychromatic418967fa.accept_17_11_6_5_1_3662 28 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 108 243 27 1 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 108 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 26 108 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 243 (Polychromatic418967fa.accept_10_5_8_3_1_229 25 108
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 243 3 8 36 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 108 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 108 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 108 243 3 7 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 108 243 (Polychromatic418967fa.accept_13_7_4_9_1_1865
  20 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 243
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 19 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 243 9 2 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 243 (Polychromatic418967fa.accept_19_17_13_15_1_1402 17 108 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 16
  108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 108 243 3 5 36 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 108 243
  (Polychromatic418967fa.accept_19_14_13_15_1_2532 14 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 108 243 (Polychromatic418967fa.accept_20_13_8_3_1_11818 13 108 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 243 3 4 36 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 243
  (Polychromatic418967fa.accept_10_1_8_3_1_947 11 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 108 243 (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 108 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 108 243 9 1 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 108 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 108 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 243
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 108 243 3 2 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 108 243 (Polychromatic418967fa.accept_10_5_8_3_1_229 5 108 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 243 (Polychromatic418967fa.accept_16_4_12_3_1_2180 4 108
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 108 243 3 1 36 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 108 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 108 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 108 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 108 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 243 (allA_succ_of_accept 106 107 243 (accept_3_4 106 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 105 107 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 104 107
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 243 (accept_3_4 103 107
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 102 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 101 107 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 243 (accept_3_4 100 107 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 243 (Polychromatic418967fa.accept_13_8_3_9_1_5269 99 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 98 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 107 243 (accept_3_4 97 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 107 243 (Polychromatic418967fa.accept_10_6_7_3_1_547 96 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 107 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 95 107 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 243 (accept_3_4 94 107 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 107 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 93 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 243 (accept_3_4 91 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 243 (Polychromatic418967fa.accept_13_12_3_9_1_4341 90 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 107 243 (Polychromatic418967fa.accept_15_14_2_3_1_1980 89 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 243 (accept_3_4 88 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 87 107 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 86 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 243 (accept_3_4 85 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 243 (Polychromatic418967fa.accept_10_4_7_3_1_54 84 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 243 (Polychromatic418967fa.accept_13_5_3_9_1_1189 83 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 243 (accept_3_4 82 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 81 107 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 243 (accept_3_4 79 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 243 (Polychromatic418967fa.accept_16_14_11_3_1_4249 78 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 243 (Polychromatic418967fa.accept_13_12_3_9_1_4341 77 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 243 (accept_3_4 76 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 75 107
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 74 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 243 (accept_3_4 73 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 243 (Polychromatic418967fa.accept_13_7_3_9_1_1142 72 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 243 (Polychromatic418967fa.accept_13_6_3_9_1_1827 71 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 243 (accept_3_4 70 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 69 107
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 243 (accept_3_4 67 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 65 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 243 (accept_3_4 64 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 243 (Polychromatic418967fa.accept_14_7_9_5_1_529 63 107
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 243 (accept_3_4 61 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 107 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 243 (accept_3_4 58 107 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 243 (accept_3_4 55 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 243 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 107 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 243 (accept_3_4 52 107 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 243 (Polychromatic418967fa.accept_13_12_3_9_1_4341 51 107 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 243 (accept_3_4 49 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 243 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 243 (Polychromatic418967fa.accept_13_8_3_9_1_5269 47 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 243 (accept_3_4 46 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 107 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 243 (accept_3_4 43 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 243 (Polychromatic418967fa.accept_15_12_2_3_1_1146 42 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 243 (Polychromatic418967fa.accept_13_2_3_9_1_2610 41 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 243 (accept_3_4 40 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 107 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 243 (accept_3_4 37 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 243 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 35 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 243 (accept_3_4 34 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 107
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 243 (accept_3_4 31 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 243 (Polychromatic418967fa.accept_16_14_11_3_1_4249 30 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 243 (Polychromatic418967fa.accept_15_14_2_3_1_1980 29 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 243 (accept_3_4 28 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 243 (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 107
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 243 (accept_3_4 25 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 243 (Polychromatic418967fa.accept_16_7_11_3_1_1330 23 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 243 (accept_3_4 22 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 107
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 243 (accept_3_4 19 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 107 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 243 (accept_3_4 16 107 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 243 (accept_3_4 13 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 243 (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 107 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 243 (accept_3_4 10 107 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 243 (accept_3_4 7 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 243 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 107 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 243 (accept_3_4 4 107 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 107 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 243 (accept_3_4 1 107 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 243 (allA_succ_of_accept 105 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 106 243 (accept_3_5 104 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 106 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 103 106
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 106 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 102 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 106 243 (accept_3_5 101 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 106 243 (Polychromatic418967fa.accept_19_5_11_15_1_2460 100 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 106 243 (Polychromatic418967fa.accept_10_9_6_3_1_545 99 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 106 243 (accept_3_5 98 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 106 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 106 243
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 96 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 106 243 (accept_3_5 95 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 106 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 94 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 106 243 (accept_3_5 92 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 106 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 106 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 90 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 106 243 (accept_3_5 89 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 106 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 88 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 106 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 106 243 (accept_3_5 86 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 106 243
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 84 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 106 243 (accept_3_5 83 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 106 243 (Polychromatic418967fa.accept_19_6_11_15_1_2527 82 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 106 243 (accept_3_5 80 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 106 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 106 243
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 78 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 106 243 (accept_3_5 77 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 106 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 106 243 (Polychromatic418967fa.accept_30_15_16_3_1_3855 75 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 106 243 (accept_3_5 74 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 106 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 106 243
  (Polychromatic418967fa.accept_11_6_7_1_1_564 72 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 106 243 (accept_3_5 71 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 106 243 (Polychromatic418967fa.accept_13_5_2_9_1_1195 70 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 106 243 (accept_3_5 68 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 106 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 106 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 66 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 106 243 (accept_3_5 65 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 106 243 (Polychromatic418967fa.accept_15_4_1_3_1_1922 64 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 106 243 (Polychromatic418967fa.accept_13_11_2_9_1_2640 63 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 106 243 (accept_3_5 62 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 106 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 106 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 60 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 106 243 (accept_3_5 59 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 106 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 58 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 106 243 (accept_3_5 56 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 106 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 106 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 106 243 (accept_3_5 53 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 106 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 106 243 (Polychromatic418967fa.accept_15_6_1_3_1_2852 51 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 243 (accept_3_5 50 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 106 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 106 243 (accept_3_5 47 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 106 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 243 (accept_3_5 44 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 106 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 243 (accept_3_5 41 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 243 (Polychromatic418967fa.accept_13_1_2_9_1_1186 40 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 243 (accept_3_5 38 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 243
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 36 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 106 243 (accept_3_5 35 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 106 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 243 (accept_3_5 32 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 106 243 (accept_3_5 29 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 106 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 243 (accept_3_5 26 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 243 (accept_3_5 23 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 243 (Polychromatic418967fa.accept_23_22_14_13_1_14654 22 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 243 (accept_3_5 20 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 106 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 243 (accept_3_5 17 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 243 (Polychromatic418967fa.accept_13_3_2_9_1_1187 16 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 243 (Polychromatic418967fa.accept_18_15_16_9_1_4299 15 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 243 (accept_3_5 14 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 106 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 243
  (Polychromatic418967fa.accept_16_12_10_3_1_4209 12 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 106 243 (accept_3_5 11 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 106 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 106 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 243 (accept_3_5 8 106 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7
  106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 243 (accept_3_5 5 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 106 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 243 (accept_3_5 2 106 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 243 (allA_succ_of_accept 104 105 243 (Polychromatic418967fa.accept_11_5_6_1_1_988 104 105 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 243
  (Polychromatic418967fa.accept_12_7_9_3_1_767 103 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 105 243 3 34 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 105 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 101 105 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 105 243
  (Polychromatic418967fa.accept_14_2_7_5_1_5450 100 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 105 243 3 33 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 105 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 105 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 243 (Polychromatic418967fa.accept_10_7_5_3_1_542
  97 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 105 243 3 32 35 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 105 243
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 95 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 105 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 105 243 3 31 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 105 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408
  92 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 243
  (Polychromatic418967fa.accept_12_7_9_3_1_767 91 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 105 243 3 30 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 105 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 89 105 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 243 (Polychromatic418967fa.accept_10_8_5_3_1_543
  88 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 105 243 3 29 35 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 105 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 105 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 85 105 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 105 243 3 28 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 105 243 (Polychromatic418967fa.accept_12_11_9_3_1_792
  83 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 105 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 82 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 105 243 3 27 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 105 243 (Polychromatic418967fa.accept_13_2_1_9_1_1174 80 105 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 243
  (Polychromatic418967fa.accept_12_7_9_3_1_767 79 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 105 243 3 26 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 105 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 77 105 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 105 243
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 76 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 105 243 3 25 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 105 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 105 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 243 (Polychromatic418967fa.accept_11_7_6_1_1_2182
  73 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 105 243 3 24 35 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 105 243
  (Polychromatic418967fa.accept_11_5_6_1_1_988 71 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 105 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 105 243 3 23 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 105 243 (Polychromatic418967fa.accept_10_8_5_3_1_543
  68 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 67 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 105 243 3 22 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 105 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 65 105 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 243
  (Polychromatic418967fa.accept_18_10_15_9_1_1054 64 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 105 243 3 21 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 105 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 105 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 61 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 105 243 3 20 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 105 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 59 105 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 105 243 3 19 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 105 243 (Polychromatic418967fa.accept_24_8_9_3_1_9684 56 105 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 243
  (Polychromatic418967fa.accept_12_7_9_3_1_767 55 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 105 243 3 18 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 105 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 105 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408
  52 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 105 243 3 17 35 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 105 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 105 243 (Polychromatic418967fa.accept_11_5_6_1_1_988 49 105 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 105 243 3 16 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 105 243 (Polychromatic418967fa.accept_10_7_5_3_1_542
  47 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 105 243 3 15 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 105 243 (Polychromatic418967fa.accept_13_5_1_9_1_618 44 105 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 243 (Polychromatic418967fa.accept_12_7_9_3_1_767
  43 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 105 243 3 14 35 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 105 243
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 243 (Polychromatic418967fa.accept_11_7_6_1_1_2182 40 105 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 105 243 3 13 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 105 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 37 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 105 243 3 12 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 105 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 105 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 105 243 3 11 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 105 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408 32 105 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 243
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 105 243 3 10 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 105 243 (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 105 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 243
  (Polychromatic418967fa.accept_10_8_5_3_1_543 28 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 105 243 3 9 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 105 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 105 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 105
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 105 243 3 8 35 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 105 243
  (Polychromatic418967fa.accept_12_11_9_3_1_792 23 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 105 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 243 3 7 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 105 243
  (Polychromatic418967fa.accept_22_20_17_1_1_14653 20 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 105 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 105 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 105 243 3 6 35 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 105 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 17 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 243 (Polychromatic418967fa.accept_11_5_6_1_1_988 16 105 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 243 3 5 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 105 243 3 4 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 105 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 105 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 105 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 105 243 3 3 35 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 243
  (Polychromatic418967fa.accept_10_8_5_3_1_543 8 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 105 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 105 243 3 2 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 105 243 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 105 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 243
  (Polychromatic418967fa.accept_18_4_15_9_1_6882 4 105 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 105 243 3 1 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 105 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 105 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 243 (allA_succ_of_accept 103 104 243 (accept_3_4 103 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 104 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 102 104 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 104 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 101 104
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 104 243 (accept_3_4 100 104
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 104 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 99 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 104 243 (Polychromatic418967fa.accept_19_3_9_15_1_9240 98 104 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 104 243 (accept_3_4 97 104 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 104 243 (Polychromatic418967fa.accept_18_6_14_9_1_3039 96 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 104 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 104 243 (accept_3_4 94 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 104 243 (Polychromatic418967fa.accept_16_13_8_3_1_5374 93 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 104 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 92 104 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 104 243 (accept_3_4 91 104 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 104 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 90 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 104 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 89 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 104 243 (accept_3_4 88 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 104 243 (Polychromatic418967fa.accept_10_7_4_3_1_560 87 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 104 243 (Polychromatic418967fa.accept_15_11_14_3_1_1965 86 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 104 243 (accept_3_4 85 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 104 243 (Polychromatic418967fa.accept_16_4_8_3_1_4206 84 104
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 104 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 104 243 (accept_3_4 82 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 104 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 104 243 (Polychromatic418967fa.accept_19_4_9_15_1_6405 80 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 104 243 (accept_3_4 79 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 104 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 78 104 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 104 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 104 243 (accept_3_4 76 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 104 243 (Polychromatic418967fa.accept_16_11_8_3_1_3183 75 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 104 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 74 104 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 104 243 (accept_3_4 73 104 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 104 243 (Polychromatic418967fa.accept_11_6_5_1_1_586 72 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 104 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 104 243 (accept_3_4 70 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 104 243 (Polychromatic418967fa.accept_10_9_4_3_1_539 69 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 104 243 (Polychromatic418967fa.accept_16_4_8_3_1_4206 68 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 104 243 (accept_3_4 67 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 104 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 104 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 104 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 104 243 (accept_3_4 64 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 104 243 (Polychromatic418967fa.accept_19_6_9_15_1_3694 63 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 104 243 (Polychromatic418967fa.accept_15_2_14_3_1_1916 62 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 104 243 (accept_3_4 61 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 104 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 104 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 104 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 104 243 (accept_3_4 58 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 104 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 104 243 (Polychromatic418967fa.accept_15_11_14_3_1_1965 56 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 104 243 (accept_3_4 55 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 104 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 104 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 104 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 104 243 (accept_3_4 52 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 104 243 (Polychromatic418967fa.accept_19_13_9_15_1_11989 51 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 50 104 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 50 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 104 243 (accept_3_4 49 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 104 243 (Polychromatic418967fa.accept_17_14_2_5_1_3560 48 104
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 104 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 104 243 (accept_3_4 46 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 104 243 (Polychromatic418967fa.accept_16_13_8_3_1_5374 45 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 104 243 (Polychromatic418967fa.accept_16_12_8_3_1_4241 44 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 104 243 (accept_3_4 43 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 104 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 104 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 104 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 104 243 (accept_3_4 40 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 104 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 104 243 (Polychromatic418967fa.accept_32_6_8_19_1_14652 38 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 104 243 (accept_3_4 37 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 104 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 104 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 104 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 104 243 (accept_3_4 34 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 104 243 (Polychromatic418967fa.accept_17_16_2_5_1_6031 33 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 104 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 104 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 104 243 (accept_3_4 31 104 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 104 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 104 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 104 243 (accept_3_4 28 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 104 243 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 104 243 (Polychromatic418967fa.accept_15_11_14_3_1_1965 26 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 104 243 (accept_3_4 25 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 104 243 (Polychromatic418967fa.accept_18_6_14_9_1_3039 24 104
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 104 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 104 243 (accept_3_4 22 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 104 243 (Polychromatic418967fa.accept_16_5_8_3_1_4240 21 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 104 243 (Polychromatic418967fa.accept_16_4_8_3_1_4206 20 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 104 243 (accept_3_4 19 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 104 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 104 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 104 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 104 243 (accept_3_4 16 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 104 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 104 243 (Polychromatic418967fa.accept_17_14_2_5_1_3560 14 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 104 243 (accept_3_4 13 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 104 243 (Polychromatic418967fa.accept_16_12_8_3_1_4241 12 104
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 104 243 (accept_3_4 10 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  104 243 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 104 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 104 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 104 243 (accept_3_4 7 104 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 104 243 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 104 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 104 243 (accept_3_4 4 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  104 243 (Polychromatic418967fa.accept_17_3_2_5_1_2556 3 104 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 104 243 (Polychromatic418967fa.accept_15_2_14_3_1_1916 2 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 104 243 (accept_3_4 1 104 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 104
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 243 (allA_succ_of_accept 102 103 243 (Polychromatic418967fa.accept_15_12_13_3_1_1915 102 103 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 243 (accept_3_5 101 103 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 103 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 103
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 243
  (Polychromatic418967fa.accept_13_8_12_9_1_1168 99 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 243 (accept_3_5 98 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 243 (Polychromatic418967fa.accept_19_2_8_15_1_2447 97 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 243 (Polychromatic418967fa.accept_11_8_4_1_1_1000 96 103 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 243 (accept_3_5 95 103 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 103 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 243
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 93 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 243 (accept_3_5 92 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 243 (Polychromatic418967fa.accept_15_1_13_3_1_2002 91 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 243 (Polychromatic418967fa.accept_16_10_7_3_1_6601 90 103 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 243 (accept_3_5 89 103 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 103 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 243
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 87 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 103 243 (accept_3_5 86 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 103 243 (Polychromatic418967fa.accept_11_8_4_1_1_1000 85 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 103 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 103 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 243 (accept_3_5 83 103 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 82
  103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 243
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 81 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 243 (accept_3_5 80 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 243 (Polychromatic418967fa.accept_16_15_7_3_1_4273 79 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 243 (Polychromatic418967fa.accept_18_6_13_9_1_4218 78 103 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 243 (accept_3_5 77 103 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 103 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 243
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 75 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 103 243 (accept_3_5 74 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 103 243 (Polychromatic418967fa.accept_13_8_12_9_1_1168 73 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 103 243 (Polychromatic418967fa.accept_15_12_13_3_1_1915 72 103
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 243 (accept_3_5 71 103
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 243
  (Polychromatic418967fa.accept_6_4_1_3_1_77 70 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 103 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309 69 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 103 243 (accept_3_5 68 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 103 243 (Polychromatic418967fa.accept_17_16_1_5_1_2600 67 103 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 103 243
  (Polychromatic418967fa.accept_31_4_10_26_1_14651 66 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 103 243 (accept_3_5 65 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 103 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 243 (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 103
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 103 243 (accept_3_5 62 103
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 103 243
  (Polychromatic418967fa.accept_15_1_13_3_1_2002 61 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 103 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 243 (accept_3_5 59 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 103 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 103 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  57 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 243 (accept_3_5 56
  103 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 103 243
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 55 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 103 243 (Polychromatic418967fa.accept_15_9_13_3_1_535 54 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 243 (accept_3_5 53 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 103 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 103 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 243
  (Polychromatic418967fa.accept_21_9_19_12_1_10140 51 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 103 243 (accept_3_5 50 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 103 243 (Polychromatic418967fa.accept_13_10_12_9_1_1837 49 103 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 243
  (Polychromatic418967fa.accept_21_6_19_12_1_3981 48 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 103 243 (accept_3_5 47 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 103 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 103
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 243 (accept_3_5 44 103
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 243
  (Polychromatic418967fa.accept_16_11_7_3_1_3163 43 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 103 243 (Polychromatic418967fa.accept_13_3_12_9_1_1193 42 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 243 (accept_3_5 41 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 103 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 103 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 243 (Polychromatic418967fa.accept_15_9_13_3_1_535
  39 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 243 (accept_3_5 38
  103 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 243
  (Polychromatic418967fa.accept_34_3_1_5_1_14650 37 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 103 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 243 (accept_3_5 35 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 103 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 103 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  33 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 243 (accept_3_5 32
  103 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 243
  (Polychromatic418967fa.accept_15_1_13_3_1_2002 31 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 103 243 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 243 (accept_3_5 29 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 103 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 103 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 243
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 103 243 (accept_3_5 26 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 103 243 (Polychromatic418967fa.accept_15_10_13_3_1_4816 25 103 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 243 (Polychromatic418967fa.accept_15_9_13_3_1_535
  24 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 243 (accept_3_5 23
  103 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 243
  (Polychromatic418967fa.accept_6_4_1_3_1_77 22 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 103 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 243 (accept_3_5 20 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 103 243 (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 103 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 243
  (Polychromatic418967fa.accept_21_18_19_12_1_3982 18 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 103 243 (accept_3_5 17 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 103 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 103 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 243 (Polychromatic418967fa.accept_16_15_7_3_1_4273 15 103
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 243 (accept_3_5 14 103
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 243
  (Polychromatic418967fa.accept_26_13_25_9_1_14649 13 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 103 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 243 (accept_3_5 11 103 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 103 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 243
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 243 (accept_3_5 8 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 243 (Polychromatic418967fa.accept_19_7_8_15_1_2448 7 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 243 (Polychromatic418967fa.accept_17_6_1_5_1_3552 6 103 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 243 (accept_3_5 5 103 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 103 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 243
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 243 (accept_3_5 2 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 243 (Polychromatic418967fa.accept_15_1_13_3_1_2002 1 103 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 243 (allA_succ_of_accept 101 102 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 102 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 102 243 (Polychromatic418967fa.accept_7_2_4_5_1_313
  100 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 102 243 3 33 34 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 102 243
  (Polychromatic418967fa.accept_12_2_6_3_1_331 98 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 102 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 102 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 102 243 3 32 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 102 243 (Polychromatic418967fa.accept_10_5_2_3_1_239
  95 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 102 243
  (Polychromatic418967fa.accept_12_10_6_3_1_786 94 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 102 243 3 31 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 102 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 92 102 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910
  91 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 102 243 3 30 34 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 102 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 102 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 88 102 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 102 243 3 29 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 102 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 86
  102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 102 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 85 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 243 3 28 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 83 102 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 102 243 (Polychromatic418967fa.accept_12_10_6_3_1_786
  82 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 102 243 3 27 34 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 102 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 80 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 102 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 79 102 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 102 243 3 26 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 102 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 77
  102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 102 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 76 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 102 243 3 25 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 102 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 74 102 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 73
  102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 102 243 3 24 34 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 102 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 71 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 102 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 70 102 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 102 243 3 23 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 102 243 (Polychromatic418967fa.accept_11_2_3_1_1_244
  68 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 243
  (Polychromatic418967fa.accept_13_2_11_9_1_591 67 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 243 3 22 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 102 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 64
  102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 102 243 3 21 34 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 102 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 62 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 102 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 102 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 102 243 3 20 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 102 243 (Polychromatic418967fa.accept_13_7_11_9_1_1858
  59 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 102 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 58 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 102 243 3 19 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 102 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 56 102 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 243 (Polychromatic418967fa.accept_7_6_4_5_1_314
  55 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 102 243 3 18 34 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 102 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 102 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 52 102 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 102 243 3 17 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 102 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 50
  102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 243 3 16 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 243 (Polychromatic418967fa.accept_13_8_11_9_1_593 47 102 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 243
  (Polychromatic418967fa.accept_11_2_3_1_1_244 46 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 102 243 3 15 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 102 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 102 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 43
  102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 102 243 3 14 34 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 102 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 102 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 102 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 102 243 3 13 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 102 243 (Polychromatic418967fa.accept_12_2_6_3_1_331
  38 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 243 3 12 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 243 (Polychromatic418967fa.accept_10_5_2_3_1_239 35 102 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 243 (Polychromatic418967fa.accept_7_6_4_5_1_314
  34 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 102 243 3 11 34 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 102 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 102 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 102 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 102 243 3 10 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 102 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 243
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 102 243 3 9 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 102 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 102 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 102 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 102 243 3 8 34 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 102 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 102 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 102 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 102 243 3 7 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 102 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 20
  102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 243
  (Polychromatic418967fa.accept_20_19_2_3_1_4486 19 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 243 3 6 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 102 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 102 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 102 243 3 5 34 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 102 243
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 102 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 243 3 4 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910
  11 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 243
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 102 243 3 3 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 102 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 102 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 243 (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 102
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 243 3 2 34 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 102 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 102 243 3 1 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 102 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 102 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 102
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 243 (allA_succ_of_accept 100 101 243 (accept_3_4 100 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 99 101 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 101 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 243 (accept_3_4 97 101 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 243
  (Polychromatic418967fa.accept_14_12_3_5_1_1868 96 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 101 243 (Polychromatic418967fa.accept_23_3_9_13_1_14648 95 101 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 101 243 (accept_3_4 94 101 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 101 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 93 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 101 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 101 243 (accept_3_4 91 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 101 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 101 243 (Polychromatic418967fa.accept_15_14_11_3_1_1957 89 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 101 243 (accept_3_4 88 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 101 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 87 101
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 101 243 (accept_3_4 85 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 101 243 (Polychromatic418967fa.accept_13_6_10_9_1_4329 84 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 101 243 (Polychromatic418967fa.accept_15_8_11_3_1_3847 83 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 101 243 (accept_3_4 82 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 101 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 81 101
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 101 243 (accept_3_4 79 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 101 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 101 243 (Polychromatic418967fa.accept_13_12_10_9_1_1166 77 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 243 (accept_3_4 76 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 243 (Polychromatic418967fa.accept_22_9_13_1_1_8400 75 101
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 101 243 (accept_3_4 73 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 101 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 101 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 101 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 243 (accept_3_4 70 101 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 69 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 101 243 (accept_3_4 67 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 101 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 101 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 101 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 243 (accept_3_4 64 101 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 243 (Polychromatic418967fa.accept_26_11_23_9_1_14647 63 101 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 101 243 (accept_3_4 61 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 101 243 (Polychromatic418967fa.accept_24_12_5_3_1_2674 60 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 243 (Polychromatic418967fa.accept_15_14_11_3_1_1957 59 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 243 (accept_3_4 58 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 101 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 243 (accept_3_4 55 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 243 (Polychromatic418967fa.accept_13_1_10_9_1_215 53 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 243 (accept_3_4 52 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 101 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 243 (accept_3_4 49 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 243 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 47 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 243 (accept_3_4 46 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 101
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 243 (accept_3_4 43 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 243 (Polychromatic418967fa.accept_31_10_8_26_1_14646 41 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 243 (accept_3_4 40 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 243 (Polychromatic418967fa.accept_23_16_9_13_1_14645 39
  101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 243 (accept_3_4 37 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 243 (Polychromatic418967fa.accept_17_1_16_5_1_3670 35 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 243 (accept_3_4 34 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 101
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 243 (accept_3_4 31 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 101 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 243 (accept_3_4 28 101 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 243 (Polychromatic418967fa.accept_13_1_10_9_1_215 27 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 243 (accept_3_4 25 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 243 (Polychromatic418967fa.accept_16_8_5_3_1_4297 24 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 101 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 243 (accept_3_4 22 101 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 101 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 243 (accept_3_4 19 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 243 (Polychromatic418967fa.accept_25_17_1_18_1_9384 17 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 243 (accept_3_4 16 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 101 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 243 (accept_3_4 13 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 243 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 243 (Polychromatic418967fa.accept_17_11_16_5_1_3612 11 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 243 (accept_3_4 10 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 101 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 243 (accept_3_4 7 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 243 (Polychromatic418967fa.accept_19_5_6_15_1_10686 5 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 243 (accept_3_4 4 101 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 101 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 243 (accept_3_4 1 101 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 243 (allA_succ_of_accept 99 100 243 (Polychromatic418967fa.accept_15_9_10_3_1_2845 99 100 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 100 243 (accept_3_5 98 100 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 100 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 97 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 100 243
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 96 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 100 243 (accept_3_5 95 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 100 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 94 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 100 243 (Polychromatic418967fa.accept_19_17_5_15_1_7921 93 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 100 243 (accept_3_5 92 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 100 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 100 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 100 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 90 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 100 243 (accept_3_5 89 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 100 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 88 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 100 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 87 100 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 100 243 (accept_3_5 86 100 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 100 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 100 243
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 84 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 100 243 (accept_3_5 83 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 100 243 (Polychromatic418967fa.accept_15_7_10_3_1_2891 82 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 100 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 81 100 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 100 243 (accept_3_5 80 100 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 100 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 100 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 78 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 100 243 (accept_3_5 77 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 100 243 (Polychromatic418967fa.accept_16_12_4_3_1_4295 76 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 100 243 (Polychromatic418967fa.accept_17_7_15_5_1_3649 75 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 100 243 (accept_3_5 74 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 100 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 100 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 100 243
  (Polychromatic418967fa.accept_16_8_4_3_1_3146 72 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 100 243 (accept_3_5 71 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 100 243 (Polychromatic418967fa.accept_16_6_4_3_1_2189 70 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 100 243 (Polychromatic418967fa.accept_15_9_10_3_1_2845 69 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 100 243 (accept_3_5 68 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 100 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 100 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 100 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 66 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 100 243 (accept_3_5 65 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 100 243 (Polychromatic418967fa.accept_17_13_15_5_1_3650 64 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 100 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 100 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 100 243 (accept_3_5 62 100 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 100 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 100 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 60 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 100 243 (accept_3_5 59 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 100 243 (Polychromatic418967fa.accept_15_13_10_3_1_1952 58 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 100 243 (Polychromatic418967fa.accept_22_13_12_1_1_11641 57 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 100 243 (accept_3_5 56 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 100 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 100 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 100 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 54 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 100 243 (accept_3_5 53 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 100 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 100 243 (Polychromatic418967fa.accept_15_6_10_3_1_2844 51 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 100 243 (accept_3_5 50 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 100 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 100 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 100 243
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 48 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 100 243 (accept_3_5 47 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 100 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 100 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 100 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 100 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 100 243 (accept_3_5 44 100 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 100 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 43
  100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 100 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 100 243 (accept_3_5 41 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 100 243 (Polychromatic418967fa.accept_16_8_4_3_1_3146 40 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 100 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 100 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 100 243 (accept_3_5 38 100 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 100 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 100 243
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 36 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 100 243 (accept_3_5 35 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 100 243 (Polychromatic418967fa.accept_26_8_22_9_1_14644 34 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 100 243 (Polychromatic418967fa.accept_16_1_4_3_1_3148 33 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 100 243 (accept_3_5 32 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 100 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 100 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 100 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 100 243 (accept_3_5 29 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 100 243 (Polychromatic418967fa.accept_15_13_10_3_1_1952 28 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 100 243 (Polychromatic418967fa.accept_17_10_15_5_1_3606 27 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 100 243 (accept_3_5 26 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 100 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 100 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 100 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 100 243 (accept_3_5 23 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 100 243 (Polychromatic418967fa.accept_15_7_10_3_1_2891 22 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 100 243 (Polychromatic418967fa.accept_14_7_2_5_1_4528 21 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 100 243 (accept_3_5 20 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 100 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 100 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 100 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 100 243 (accept_3_5 17 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 100 243 (Polychromatic418967fa.accept_22_16_12_1_1_13174 16 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 100 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 100 243 (accept_3_5 14 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 100 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 100 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 100 243
  (Polychromatic418967fa.accept_16_12_4_3_1_4295 12 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 100 243 (accept_3_5 11 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 100 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 100 243 (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 100 243 (accept_3_5 8 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 100 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 100 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 100 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 100 243 (accept_3_5 5 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  100 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 100 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 100 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 100 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 243 (accept_3_5 2 100 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 100 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 100 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_243_segment_000)))))))))))))))))))))))))))))))))))))))))))


